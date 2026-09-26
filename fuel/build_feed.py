#!/usr/bin/env python3
"""Trata fuel feed v1. Python 3.11+, standard library only; no keys or user data.

Public sources: ANRE (MD), Bemol (optional 98), Monitorul Preturilor (RO).
The private aggregator fallback is deliberately disabled: its current terms
forbid automated collection without written permission. TLS verification stays on.
"""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
from datetime import date, datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sys
from urllib.parse import urlencode
from urllib.request import Request, urlopen
from zoneinfo import ZoneInfo

VERSION = 1
FUELS = ('petrol', 'diesel', 'lpg', 'petrolPremium', 'dieselPremium')
TOP = {'MD': ('lukoil', 'rompetrol', 'vento', 'petrom', 'bemol'),
       'RO': ('petrom', 'omv', 'rompetrol', 'lukoil', 'mol')}
CURRENCY = {'MD': 'MDL', 'RO': 'RON'}
TZ = {'MD': 'Europe/Chisinau', 'RO': 'Europe/Bucharest'}
RO_PRODUCTS = {'11': 'petrol', '12': 'petrolPremium', '21': 'diesel',
               '22': 'dieselPremium', '31': 'lpg'}
RO_BRANDS = set(TOP['RO']) | {'socar', 'gazprom'}
# Fixed public city centres, never a device location. Radius is limited to 5 km.
RO_POINTS = ((26.1025, 44.4268), (23.5899, 46.7712), (27.6014, 47.1585))
MD_API = 'https://api.ecarburanti.anre.md/public/'
RO_API = 'https://monitorulpreturilor.info/pmonsvc/Gas/GetGasItemsByLatLon?'
D = Decimal
WARNINGS = []
REQUESTS = []


def warn(message):
    WARNINGS.append(message)
    print('::warning::' + message.replace('\n', ' ').replace('\r', ' '), file=sys.stderr)


def request(url, is_json=True):
    req = Request(url, headers={'Accept': 'application/json' if is_json else 'text/html',
                              'User-Agent': 'TrataFuelFeed/1.0 (+https://memotvoret.github.io/trata/)'})
    # System trust store, certificate and hostname checks enabled. No unverified fallback.
    with urlopen(req, timeout=40) as response:
        data = response.read(5_000_001)
        if len(data) > 5_000_000:
            raise ValueError('source response exceeds 5 MB')
        REQUESTS.append({'url': url, 'status': response.status, 'bytes': len(data)})
    text = data.decode('utf-8-sig')
    return json.loads(text, parse_float=D) if is_json else text


def number(value, country, fuel):
    if isinstance(value, bool) or value is None:
        return None
    try:
        value = D(str(value).strip().replace(',', '.'))
    except (InvalidOperation, ValueError):
        return None
    # Premium uses the same broad sanity bounds, but never the standard fuel cap.
    low, high = ((5, 40) if fuel == 'lpg' else (10, 80)) if country == 'MD' else (
        (2, 10) if fuel == 'lpg' else (4, 20))
    if not value.is_finite() or not D(low) <= value <= D(high):
        return None
    return value.quantize(D('.01'), rounding=ROUND_HALF_UP)


def mode(values):
    counts = Counter(values)
    if not counts:
        return None
    # Deterministic tie: cheaper of equally frequent observations. Log/sample in report.
    return min(counts, key=lambda value: (-counts[value], value))


def average(brands, country):
    result = {}
    for fuel in FUELS:
        values = [brands[b][fuel] for b in TOP[country] if fuel in brands.get(b, {})]
        if len(values) >= 2:
            result[fuel] = (sum(values) / len(values)).quantize(D('.01'), rounding=ROUND_HALF_UP)
    return result


def reject_isolated_jumps(brands, previous, current_day):
    if not previous or date.fromisoformat(previous['day']) != current_day - timedelta(days=1):
        return brands
    rejected = set()
    for brand, fuels in brands.items():
        for fuel, value in fuels.items():
            old = previous['brands'].get(brand, {}).get(fuel)
            if old and abs(value / D(str(old)) - 1) > D('.15'):
                peers = [(b, p) for b, p in brands.items() if b != brand
                         and fuel in p and fuel in previous['brands'].get(b, {})]
                other_jumps = any(abs(p[fuel] / D(str(previous['brands'][b][fuel])) - 1) > D('.15')
                                  for b, p in peers)
                if not other_jumps:
                    rejected.add(brand)
    for brand in rejected:
        warn(f'Isolated >15% one-day jump: drop network {brand}')
        brands.pop(brand)
    return brands


def md_brand(station):
    name = str(station.get('station_name') or '').casefold()
    company = str(station.get('company_name') or '').casefold()
    for text in (name, company):
        for brand in TOP['MD'] + ('now', 'tlx', 'avante'):
            if re.search(r'(?<![a-z])' + brand + r'(?![a-z])', text):
                return brand
    return None


class BemolParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.field = None
        self.buf = ''
        self.label = ''
        self.grade = ''
        self.prices = {}

    def handle_starttag(self, tag, attrs):
        classes = dict(attrs).get('class', '').split()
        if tag == 'p':
            self.field = next((c for c in classes if c in ('item__name', 'item__num', 'actually__price')), None)
            self.buf = ''

    def handle_data(self, data):
        if self.field:
            self.buf += data

    def handle_endtag(self, tag):
        if tag != 'p':
            return
        if self.field == 'item__name':
            self.label, self.grade = self.buf.strip(), ''
        elif self.field == 'item__num':
            self.grade = self.buf.strip()
        elif self.field == 'actually__price':
            self.prices[(self.label.casefold(), self.grade)] = self.buf.strip()
        self.field = None


def history_points(payload, fuel, today):
    if not isinstance(payload, dict) or payload.get('status') != 'success':
        raise ValueError('MD history status is not success')
    result = {}
    for timestamp, raw in payload.get('data', []):
        # Source UNIX dates denote the publication day. Applicability starts next day.
        published = datetime.fromtimestamp(float(timestamp) / 1000, timezone.utc).date()
        effective = published + timedelta(days=1)
        value = number(raw, 'MD', fuel)
        if value is not None and effective <= today:
            result[effective] = value
    if not result:
        raise ValueError('MD history has no usable points')
    return result


def expand_history(points, start, end):
    current = {}
    result = {}
    first = min(min(p) for p in points.values())
    day = first
    while day <= end:
        for fuel, rows in points.items():
            if day in rows:
                current[fuel] = (day, rows[day])
        # Bridge weekends and holidays, but never manufacture long missing periods.
        cap = {fuel: value for fuel, (since, value) in current.items() if (day-since).days <= 6}
        if day >= start and set(cap) == {'petrol', 'diesel'}:
            result[day.isoformat()] = {'day': day.isoformat(), 'brands': {}, 'average': cap.copy(), 'cap': cap}
        day += timedelta(days=1)
    return result


def collect_md(today, existing):
    # Bootstrap once; thereafter fetch only the gap plus one week of context.
    last = max(existing, default='2021-09-08')
    start = max(date(2021, 9, 1), date.fromisoformat(last) - timedelta(days=7))
    points = {}
    for fuel, fid in (('petrol', 2), ('diesel', 3)):
        url = 'https://anre.md/oil-get-table?' + urlencode({
            'firstDate': start.isoformat(), 'secondDate': today.isoformat(), 'fuelId': fid})
        points[fuel] = history_points(request(url), fuel, today)
    historical = expand_history(points, start, today)
    cap = historical.get(today.isoformat(), {}).get('cap', {}).copy()
    current_cap = request(MD_API + 'plafon/')
    cap_date = date.fromisoformat(current_cap['date'][:10])
    if cap_date <= today and (today - cap_date).days <= 6:
        endpoint = {fuel: number(current_cap.get(field), 'MD', fuel)
                    for fuel, field in (('petrol', 'b_pc'), ('diesel', 'm_pc'))}
        if None not in endpoint.values():
            if cap and cap != endpoint:
                raise ValueError('MD current cap disagrees with effective history')
            cap = endpoint
    if set(cap) != {'petrol', 'diesel'}:
        raise ValueError('MD effective cap missing (future caps cannot price today)')
    rows = request(MD_API)
    if not isinstance(rows, list):
        raise ValueError('MD station payload is not an array')
    samples = defaultdict(lambda: defaultdict(list))
    for station in rows:
        if station.get('station_status') != 1:
            continue
        brand = md_brand(station)
        if not brand:
            continue
        for fuel, field in (('petrol', 'gasoline'), ('diesel', 'diesel'), ('lpg', 'gpl')):
            value = number(station.get(field), 'MD', fuel)
            if value is None or (fuel in cap and not cap[fuel]*D('.90') <= value <= cap[fuel]*D('1.005')):
                continue
            samples[brand][fuel].append(value)
    brands = {b: {f: mode(v) for f, v in fuels.items()} for b, fuels in samples.items()}
    try:
        parser = BemolParser()
        parser.feed(request('https://www.bemol.md/ro/prices', False))
        premium = number(parser.prices.get(('premium', '98')), 'MD', 'petrolPremium')
        normal = number(parser.prices.get(('premium', '95')), 'MD', 'petrol')
        # The page has no timestamp: its 95 price must match today's cap first.
        if premium and normal == cap['petrol'] and premium >= normal and 'bemol' in brands:
            brands['bemol']['petrolPremium'] = premium
        else:
            warn('MD Bemol premium omitted: missing data or standard-price freshness check failed')
    except Exception as exc:
        warn(f'MD optional premium omitted: {type(exc).__name__}: {exc}')
    return {'day': today.isoformat(), 'brands': brands, 'average': average(brands, 'MD'), 'cap': cap}, historical


def ro_observations(payload, expected_fuel, today):
    stations = {}
    for station in payload.get('Stations', []):
        try:
            updated = datetime.strptime(station['updatedate'].strip(), '%d/%m/%Y %H:%M').date()
        except (ValueError, KeyError, TypeError):
            continue
        if 0 <= (today - updated).days <= 7:
            stations[str(station['id'])] = station
    result = {}
    for product in payload.get('Products', []):
        station_id = str(product.get('stationid', ''))
        station = stations.get(station_id)
        if not station:  # Reject orphan products and stale stations.
            continue
        brand = str(station.get('network', {}).get('id', '')).lower()
        fuel = RO_PRODUCTS.get(str(product.get('catprod', {}).get('id')))
        value = number(product.get('price'), 'RO', fuel)
        if brand not in RO_BRANDS or fuel != expected_fuel or value is None:
            continue
        if str(product.get('network', {}).get('id', '')).lower() != brand:
            continue
        # Deduplicate stations occurring in multiple fixed-radius queries.
        result[(brand, fuel, station_id, str(product.get('id', '')))] = value
    return result


def collect_ro(today):
    observations = {}
    successful = 0
    for lon, lat in RO_POINTS:
        for product_id, fuel in RO_PRODUCTS.items():
            try:
                payload = request(RO_API + urlencode({'lon':lon, 'lat':lat, 'buffer':5000,
                    'CSVGasCatalogProductIds':product_id, 'OrderBy':'dist'}))
                if not isinstance(payload, dict) or 'Stations' not in payload or 'Products' not in payload:
                    raise ValueError('no station/product arrays')
                observations.update(ro_observations(payload, fuel, today))
                successful += 1
            except Exception as exc:
                warn(f'RO fixed point {lon},{lat} / {fuel}: {type(exc).__name__}: {exc}')
    if successful == 0:
        raise ValueError('RO official source unavailable; prohibited private fallback not used')
    # Use the most widely represented premium product within each network/fuel.
    products = defaultdict(lambda: defaultdict(list))
    for (brand, fuel, station, product), value in observations.items():
        products[(brand, fuel)][product].append(value)
    brands = defaultdict(dict)
    for (brand, fuel), variants in products.items():
        selected = min(variants, key=lambda p: (-len(variants[p]), p))
        brands[brand][fuel] = mode(variants[selected])
    return {'day':today.isoformat(), 'brands':dict(brands), 'average':average(brands, 'RO')}


def validate_day(day, country, historical=False):
    date.fromisoformat(day['day'])
    assert set(day) <= {'day', 'brands', 'average', 'cap'}
    assert isinstance(day['brands'], dict) and isinstance(day['average'], dict)
    assert country == 'MD' or 'cap' not in day
    for prices in list(day['brands'].values()) + [day['average'], day.get('cap', {})]:
        for fuel, value in prices.items():
            assert fuel in FUELS and number(value, country, fuel) == value, (fuel, value)
    if historical:
        assert country == 'MD' and not day['brands'] and day['average'] == day['cap']
        return
    assert sum('petrol' in p and 'diesel' in p for p in day['brands'].values()) >= 4, 'fewer than 4 standard-fuel networks'
    assert day['average'] == average(day['brands'], country), 'incorrect top-five average'
    assert all(f in day['average'] for f in ('petrol','diesel'))
    if country == 'MD':
        for fuel, cap in day['cap'].items():
            assert abs(day['average'][fuel]/cap-1) < D('.005'), 'MD average differs from cap by >=0.5%'
            for prices in day['brands'].values():
                if fuel in prices:
                    assert cap*D('.90') <= prices[fuel] <= cap*D('1.005')
        assert day['brands'].get('lukoil', {}).get('petrol') == day['cap']['petrol'], 'MD Lukoil/cap mismatch'


def encode(obj):
    """Compact JSON with monetary numbers printed to two decimal places."""
    if isinstance(obj, D):
        if not obj.is_finite():
            raise ValueError('non-finite decimal')
        return format(obj, '.2f')
    if isinstance(obj, dict):
        return '{'+','.join(json.dumps(k,ensure_ascii=False)+':'+encode(v) for k,v in obj.items())+'}'
    if isinstance(obj, list):
        return '['+','.join(encode(v) for v in obj)+']'
    return json.dumps(obj, ensure_ascii=False, allow_nan=False)


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'), parse_float=D)


def load_days(root, country):
    result = {}
    for path in sorted((root/country).glob('????-??.json')):
        data = read_json(path)
        assert data['version']==VERSION and data['country']==country and data['currency']==CURRENCY[country]
        for day in data['days']:
            assert day['day'][:7] == path.stem
            result[day['day']] = day
    return result


def prepare_country(root, country, today, previous):
    existing = load_days(root, country)
    if country == 'MD':
        current, history = collect_md(today, existing)
    else:
        current, history = collect_ro(today), {}
    # Compare to the prior calendar day, even when refreshing today's existing entry.
    prior = existing.get((today-timedelta(days=1)).isoformat())
    current['brands'] = reject_isolated_jumps(current['brands'], prior, today)
    current['average'] = average(current['brands'], country)
    validate_day(current, country)
    for day, item in history.items():
        validate_day(item, country, historical=True)
        if day not in existing:  # Never overwrite recorded station history with a cap-only estimate.
            existing[day] = item
    existing[today.isoformat()] = current  # Replace, not append, on the second daily run.
    by_month = defaultdict(list)
    for day in sorted(existing):
        by_month[day[:7]].append(existing[day])
    files = {root/country/(month+'.json'):{'version':1,'country':country,'currency':CURRENCY[country],'days':days}
             for month,days in by_month.items()}
    return {'currency':CURRENCY[country], 'latest':current, 'months':sorted(by_month)}, files


def write_changed(path, data):
    if path.exists() and path.read_bytes() == data:
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix+'.tmp')
    tmp.write_bytes(data)
    tmp.replace(path)
    return True


def run(root, now, report_path=None):
    WARNINGS.clear()
    REQUESTS.clear()
    old = read_json(root/'latest.json') if (root/'latest.json').exists() else {'version':1,'countries':{}}
    assert old['version'] == 1
    countries = deepcopy(old['countries'])
    pending = {}
    status = {}
    for country in ('MD','RO'):
        today = now.astimezone(ZoneInfo(TZ[country])).date()
        try:
            latest, files = prepare_country(root,country,today,countries.get(country))
            countries[country] = latest
            pending.update(files)
            status[country] = {'ok':True,'day':today.isoformat(),'networks':len(latest['latest']['brands'])}
        except Exception as exc:
            warn(f'{country}: retain all previous data: {type(exc).__name__}: {exc}')
            status[country] = {'ok':False,'retainedPrevious':country in countries,'error':str(exc)}
    if not countries:
        if report_path:
            report_path.parent.mkdir(parents=True, exist_ok=True)
            report_path.write_text(json.dumps({'countries':status, 'warnings':WARNINGS,
                'requests':REQUESTS, 'changedFiles':[], 'privateFallbackEnabled':False,
                'tlsVerification':True}, ensure_ascii=False, indent=2)+'\n')
        raise RuntimeError('No validated country data available; nothing published')
    changed_months = any(not p.exists() or read_json(p) != d for p,d in pending.items())
    generated = now.astimezone(timezone.utc).isoformat(timespec='seconds').replace('+00:00','Z')
    if old.get('countries') == countries and not changed_months:
        generated = old['generatedAt']
    latest = {'version':1,'generatedAt':generated,'countries':countries}
    raw = (encode(latest)+'\n').encode('utf-8')
    assert len(raw) < 20_000
    assert json.loads(raw)['version'] == 1
    # Validate/serialize everything before the first write. The git commit publishes atomically.
    payloads = {path:(encode(data)+'\n').encode('utf-8') for path,data in pending.items()}
    changed = [str(path) for path,data in payloads.items() if write_changed(path,data)]
    if write_changed(root/'latest.json',raw):
        changed.append(str(root/'latest.json'))
    report = {'generatedAt':generated,'countries':status,'changedFiles':changed,
              'latestBytes':len(raw),'warnings':WARNINGS,'requests':REQUESTS,
              'privateFallbackEnabled':False,'tlsVerification':True}
    if report_path:
        report_path.parent.mkdir(parents=True,exist_ok=True)
        report_path.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'countries':status,'latestBytes':len(raw),'changedFiles':len(changed)},ensure_ascii=False))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'v1')
    parser.add_argument('--report',type=Path)
    args = parser.parse_args()
    run(args.output,datetime.now(timezone.utc),args.report)


if __name__ == '__main__':
    main()
