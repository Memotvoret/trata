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
import hashlib
from itertools import combinations
from statistics import median
from pathlib import Path
import re
import sys
import ssl
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
SELECTIONS = {}
MAX_AGE_DAYS = 3


def warn(message):
    WARNINGS.append(message)
    print('::warning::' + message.replace('\n', ' ').replace('\r', ' '), file=sys.stderr)


# The RO server omits its Sectigo intermediate chain. These are NOT new trust
# anchors: both are cross/issuer certificates, verified against the OS USERTrust
# root. Partial-chain trust is disabled; hostname, validity and root checks stay on.
# Official issuer downloads (public certificates, no secrets):
# http://crt.sectigo.com/SectigoPublicServerAuthenticationCADVR36.crt
# http://crt.sectigo.com/SectigoPublicServerAuthenticationRootR46_USERTrust.crt
# Chain explanation: https://www.sectigo.com/knowledge-base/detail/Access-New-Sectigo-Certificate-Chain
# Validated locally with: openssl verify -CAfile /etc/ssl/cert.pem -untrusted bundle.pem leaf.pem
RO_CHAIN_PEM = """-----BEGIN CERTIFICATE-----
MIIGTDCCBDSgAwIBAgIQOXpmzCdWNi4NqofKbqvjsTANBgkqhkiG9w0BAQwFADBf
MQswCQYDVQQGEwJHQjEYMBYGA1UEChMPU2VjdGlnbyBMaW1pdGVkMTYwNAYDVQQD
Ey1TZWN0aWdvIFB1YmxpYyBTZXJ2ZXIgQXV0aGVudGljYXRpb24gUm9vdCBSNDYw
HhcNMjEwMzIyMDAwMDAwWhcNMzYwMzIxMjM1OTU5WjBgMQswCQYDVQQGEwJHQjEY
MBYGA1UEChMPU2VjdGlnbyBMaW1pdGVkMTcwNQYDVQQDEy5TZWN0aWdvIFB1Ymxp
YyBTZXJ2ZXIgQXV0aGVudGljYXRpb24gQ0EgRFYgUjM2MIIBojANBgkqhkiG9w0B
AQEFAAOCAY8AMIIBigKCAYEAljZf2HIz7+SPUPQCQObZYcrxLTHYdf1ZtMRe7Yeq
RPSwygz16qJ9cAWtWNTcuICc++p8Dct7zNGxCpqmEtqifO7NvuB5dEVexXn9RFFH
12Hm+NtPRQgXIFjx6MSJcNWuVO3XGE57L1mHlcQYj+g4hny90aFh2SCZCDEVkAja
EMMfYPKuCjHuuF+bzHFb/9gV8P9+ekcHENF2nR1efGWSKwnfG5RawlkaQDpRtZTm
M64TIsv/r7cyFO4nSjs1jLdXYdz5q3a4L0NoabZfbdxVb+CUEHfB0bpulZQtH1Rv
38e/lIdP7OTTIlZh6OYL6NhxP8So0/sht/4J9mqIGxRFc0/pC8suja+wcIUna0HB
pXKfXTKpzgis+zmXDL06ASJf5E4A2/m+Hp6b84sfPAwQ766rI65mh50S0Di9E3Pn
2WcaJc+PILsBmYpgtmgWTR9eV9otfKRUBfzHUHcVgarub/XluEpRlTtZudU5xbFN
xx/DgMrXLUAPaI60fZ6wA+PTAgMBAAGjggGBMIIBfTAfBgNVHSMEGDAWgBRWc1hk
lfmSGrASKgRieaFAFYghSTAdBgNVHQ4EFgQUaMASFhgOr872h6YyV6NGUV3LBycw
DgYDVR0PAQH/BAQDAgGGMBIGA1UdEwEB/wQIMAYBAf8CAQAwHQYDVR0lBBYwFAYI
KwYBBQUHAwEGCCsGAQUFBwMCMBsGA1UdIAQUMBIwBgYEVR0gADAIBgZngQwBAgEw
VAYDVR0fBE0wSzBJoEegRYZDaHR0cDovL2NybC5zZWN0aWdvLmNvbS9TZWN0aWdv
UHVibGljU2VydmVyQXV0aGVudGljYXRpb25Sb290UjQ2LmNybDCBhAYIKwYBBQUH
AQEEeDB2ME8GCCsGAQUFBzAChkNodHRwOi8vY3J0LnNlY3RpZ28uY29tL1NlY3Rp
Z29QdWJsaWNTZXJ2ZXJBdXRoZW50aWNhdGlvblJvb3RSNDYucDdjMCMGCCsGAQUF
BzABhhdodHRwOi8vb2NzcC5zZWN0aWdvLmNvbTANBgkqhkiG9w0BAQwFAAOCAgEA
YtOC9Fy+TqECFw40IospI92kLGgoSZGPOSQXMBqmsGWZUQ7rux7cj1du6d9rD6C8
ze1B2eQjkrGkIL/OF1s7vSmgYVafsRoZd/IHUrkoQvX8FZwUsmPu7amgBfaY3g+d
q1x0jNGKb6I6Bzdl6LgMD9qxp+3i7GQOnd9J8LFSietY6Z4jUBzVoOoz8iAU84OF
h2HhAuiPw1ai0VnY38RTI+8kepGWVfGxfBWzwH9uIjeooIeaosVFvE8cmYUB4TSH
5dUyD0jHct2+8ceKEtIoFU/FfHq/mDaVnvcDCZXtIgitdMFQdMZaVehmObyhRdDD
4NQCs0gaI9AAgFj4L9QtkARzhQLNyRf87Kln+YU0lgCGr9HLg3rGO8q+Y4ppLsOd
unQZ6ZxPNGIfOApbPVf5hCe58EZwiWdHIMn9lPP6+F404y8NNugbQixBber+x536
WrZhFZLjEkhp7fFXf9r32rNPfb74X/U90Bdy4lzp3+X1ukh1BuMxA/EEhDoTOS3l
7ABvc7BYSQubQ2490OcdkIzUh3ZwDrakMVrbaTxUM2p24N6dB+ns2zptWCva6jzW
r8IWKIMxzxLPv5Kt3ePKcUdvkBU/smqujSczTzzSjIoR5QqQA6lN1ZRSnuHIWCvh
JEltkYnTAH41QJ6SAWO66GrrUESwN/cgZzL4JLEqz1Y=
-----END CERTIFICATE-----
-----BEGIN CERTIFICATE-----
MIIGlTCCBH2gAwIBAgIRANJ/u8HeNZ5SFq1hSVhgmcQwDQYJKoZIhvcNAQEMBQAw
gYgxCzAJBgNVBAYTAlVTMRMwEQYDVQQIEwpOZXcgSmVyc2V5MRQwEgYDVQQHEwtK
ZXJzZXkgQ2l0eTEeMBwGA1UEChMVVGhlIFVTRVJUUlVTVCBOZXR3b3JrMS4wLAYD
VQQDEyVVU0VSVHJ1c3QgUlNBIENlcnRpZmljYXRpb24gQXV0aG9yaXR5MB4XDTIx
MDMyMjAwMDAwMFoXDTM4MDExODIzNTk1OVowXzELMAkGA1UEBhMCR0IxGDAWBgNV
BAoTD1NlY3RpZ28gTGltaXRlZDE2MDQGA1UEAxMtU2VjdGlnbyBQdWJsaWMgU2Vy
dmVyIEF1dGhlbnRpY2F0aW9uIFJvb3QgUjQ2MIICIjANBgkqhkiG9w0BAQEFAAOC
Ag8AMIICCgKCAgEAk77VNlJ12AEjoBxHQknuY7a3If3EldVIKyZ8FFMQ2nn9K7ct
pNQs+uoy3UnCub0PSD17WphUr55dMXRPB/xQId2kz2hPGxJjbSWZTCqZ80gwYfqB
fB6nCErcPiscHxhMcao1jK34bug7StnllALWiYQTqm3ITzPMUJY3kjPcX4jnn1TZ
SPCYQ9Zm/Z8XOEPFAVEL1+MjDxRdWxTnS77d9MjaAzfR1jmhIVEwg7Bt1zBOlluR
8HAkq79FgWRDDb0hOi886Z4NyyC1QifM2m+b7mQwkDnNk2WBITG1I1AzNyLjOO34
MTDMRf5i+dFdMnlCh99qzFYZQE3Oqrv5tXZJlPEn+JGlg+UGs2MOgNzgElWApjtm
tDmHLcjw0NEU6eQNTQ72XVdyxTscR1ad4tX7gWGMzE2AkDRbt9cUddzYBEifwMEo
iLTpHMqnsfFWt3tJTFnlIBWohAIp+jiUaZpJBo/NH3kUFxIMg3reH7GX7vmXeCik
yESS6X0mBaZYcpt5E9gRX67FOGI0aLKGMI74kGGeMmz1BzbNokxu7Io27fLmmRVE
cMN8vJw5wLTha/eDJSNX2RKA5UnwdQ/vjescm1QotCE8/HwK/+97a3X/ix2gGQWr
+vgrgULoOLq7+6r9PeDzyt9Ol5cp7fMYVumllqy9w5CYsuD5otSmR0N8bc8CAwEA
AaOCASAwggEcMB8GA1UdIwQYMBaAFFN5v1qqK0rPVIDh2JvAnfKyA2bLMB0GA1Ud
DgQWBBRWc1hklfmSGrASKgRieaFAFYghSTAOBgNVHQ8BAf8EBAMCAYYwDwYDVR0T
AQH/BAUwAwEB/zAdBgNVHSUEFjAUBggrBgEFBQcDAQYIKwYBBQUHAwIwEQYDVR0g
BAowCDAGBgRVHSAAMFAGA1UdHwRJMEcwRaBDoEGGP2h0dHA6Ly9jcmwudXNlcnRy
dXN0LmNvbS9VU0VSVHJ1c3RSU0FDZXJ0aWZpY2F0aW9uQXV0aG9yaXR5LmNybDA1
BggrBgEFBQcBAQQpMCcwJQYIKwYBBQUHMAGGGWh0dHA6Ly9vY3NwLnVzZXJ0cnVz
dC5jb20wDQYJKoZIhvcNAQEMBQADggIBADpvBIlq7bMU0cFDT/9P9+BsgCkRgQs0
S6Bf7vJSlWMHwby0VGvxCS0hrbi0K2BINZbEbsVsgpQq04431yyoVn3Hldorgq24
RldRDOOipEZDTFB9wC9HYt1thHF00XeG2C8KC1plwoEzKAIhPvefI/C3cT0CfTXJ
uFjUbKIgSwjNjw6YHtLgoy/hd5+JLUlLco/gzFX/qWbT7tEquOMYpsNKWZj8TLqP
q6zMiG4Na6feEZte6YPXGrMWlTWN341vDedc+yxQqSug79HJUQcOZs7KyDWztmae
QxsPE49UV/8XwrfZtZaYyrs4FpD94Z4Q8dzXGL8+qEJjxgcza7W6PROaClubavd1
VKPm8+aCW77u7SxpR2TFGL6kPdxsKyFijpcunR5V79sUyROfNdzjrAcFWZXK8sbb
9FlnwuVG677JLv+ZVTX5AxLvW5OB4zt5uS+zB62wJ/Wv+jXGAttSAcJec4iFgCWH
Rvdi/jJoSzRLa3nEzx6pFIzclSCnh0u1xCeLcUBypSiPga8W+6PkuoyQq8U9qs9E
oxG5NvrvlyshwUS9yvcZRGw7Ljlx4jJH/BhIPR8kIBCQj1vna9TziZOrw1Of8hDU
bHKFG9Pm8Dp2vbjz/2JH39qvxshPKVllGfq+5klPm7yZRUYTiCMAbqwNdL/nsqF2
Rnnyp58XRStJ
-----END CERTIFICATE-----
"""


def ro_tls_context():
    context = ssl.create_default_context()
    context.load_verify_locations(cadata=RO_CHAIN_PEM)
    context.verify_flags &= ~getattr(ssl, 'VERIFY_X509_PARTIAL_CHAIN', 0)
    assert context.verify_mode == ssl.CERT_REQUIRED and context.check_hostname
    return context


def request(url, is_json=True):
    req = Request(url, headers={'Accept': 'application/json' if is_json else 'text/html',
                              'User-Agent': 'TrataFuelFeed/1.0 (+https://memotvoret.github.io/trata/)'})
    # Supplement the missing RO issuer chain only, never bypass TLS verification.
    context = ro_tls_context() if url.startswith(RO_API) else None
    with urlopen(req, timeout=40, context=context) as response:
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


def select_networks(brands, country, station_counts=None):
    eligible = {b for b, prices in brands.items() if all(f in prices for f in ('petrol', 'diesel'))}
    preferred = [b for b in TOP[country] if b in eligible]
    counts = station_counts or {}
    alternatives = sorted(eligible-set(preferred), key=lambda b: (-counts.get(b, 0), b))
    return preferred + alternatives[:5-len(preferred)]


def average_selected(brands, selected):
    result = {}
    for fuel in FUELS:
        values = [brands[b][fuel] for b in selected if fuel in brands[b]]
        if len(values) >= 2:
            result[fuel] = (sum(values) / len(values)).quantize(D('.01'), rounding=ROUND_HALF_UP)
    return result


def average(brands, country, station_counts=None):
    return average_selected(brands, select_networks(brands, country, station_counts))


def freshness_errors(countries, now):
    errors = []
    for country in CURRENCY:
        today = now.astimezone(ZoneInfo(TZ[country])).date()
        try:
            recorded = date.fromisoformat(countries[country]['latest']['day'])
            age = (today-recorded).days
            if not 0 <= age <= MAX_AGE_DAYS:
                errors.append(f'{country}: latest.day={recorded}, age={age} days; allowed 0..3. '
                              'No data published. Check sources and rerun Fuel prices and Pages.')
        except (KeyError, TypeError, ValueError):
            errors.append(f'{country}: missing or invalid latest.day; no data published.')
    return errors


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
    # Group unknown operators using a stable opaque public-feed key.
    identity = str(station.get('idno') or company).strip()
    return 'md-' + hashlib.sha256(identity.encode()).hexdigest()[:12] if identity else None


def md_station_key(station):
    # Source has no station ID. Coordinates + address deduplicate repeated records.
    fields = ('x', 'y', 'fullstreet', 'addrnum', 'bua', 'roadkm', 'roadm', 'road_side')
    return tuple(str(station.get(k) or '').strip().casefold() for k in fields)


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
        cap = {fuel: value for fuel, (since, value) in current.items() if (day-since).days <= MAX_AGE_DAYS}
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
    if cap_date <= today and (today - cap_date).days <= MAX_AGE_DAYS:
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
    station_ids = defaultdict(set)
    seen = set()
    for station in rows:
        if station.get('station_status') != 1:
            continue
        brand = md_brand(station)
        if not brand:
            continue
        key = md_station_key(station)
        if not any(key) or (brand, key) in seen:
            continue
        seen.add((brand, key))
        usable = False
        for fuel, field in (('petrol', 'gasoline'), ('diesel', 'diesel'), ('lpg', 'gpl')):
            value = number(station.get(field), 'MD', fuel)
            if value is None or (fuel in cap and not cap[fuel]*D('.90') <= value <= cap[fuel]*D('1.005')):
                continue
            samples[brand][fuel].append(value)
            usable = True
        if usable:
            station_ids[brand].add(key)
    counts = {b: len(ids) for b, ids in station_ids.items()}
    # A single independent station is not treated as a replacement network.
    samples = {b: fuels for b, fuels in samples.items() if not b.startswith('md-') or counts[b] >= 2}
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
    return {'day': today.isoformat(), 'brands': brands, 'average': average(brands, 'MD', counts), 'cap': cap, '_station_counts': counts}, historical


def ro_observations(payload, expected_fuel, today):
    stations = {}
    for station in payload.get('Stations', []):
        try:
            updated = datetime.strptime(station['updatedate'].strip(), '%d/%m/%Y %H:%M').date()
        except (ValueError, KeyError, TypeError):
            continue
        if 0 <= (today - updated).days <= MAX_AGE_DAYS:
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
        if not re.fullmatch(r'[a-z0-9][a-z0-9_-]{0,63}', brand) or fuel != expected_fuel or value is None:
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
    station_ids = defaultdict(set)
    for brand, fuel, station, product in observations:
        station_ids[brand].add(station)
    counts = {b:len(ids) for b,ids in station_ids.items()}
    return {'day':today.isoformat(), 'brands':dict(brands), 'average':average(brands, 'RO', counts), '_station_counts':counts}


def validate_day(day, country, historical=False, station_counts=None):
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
    brands = day['brands']
    eligible = {b for b,p in brands.items() if all(f in p for f in ('petrol','diesel'))}
    assert len(eligible) >= 3, 'fewer than 3 standard-fuel networks'
    assert all(f in day['average'] for f in ('petrol','diesel'))
    if station_counts is not None:
        selected = select_networks(brands, country, station_counts)
        assert day['average'] == average_selected(brands, selected), 'incorrect station-ranked top-five average'
    else:
        # v1 intentionally stores no station counts. Verify archived arithmetic against
        # an admissible selection; exact count ranking is verified during collection.
        preferred = [b for b in TOP[country] if b in eligible]
        alternatives = sorted(eligible-set(preferred))
        selected = next((preferred+list(extra) for extra in combinations(alternatives, min(5-len(preferred), len(alternatives)))
                         if average_selected(brands, preferred+list(extra)) == day['average']), None)
        assert selected is not None, 'incorrect top-five average'
    if country == 'MD':
        assert set(day.get('cap', {})) == {'petrol','diesel'}, 'missing MD cap'
        for fuel, cap in day['cap'].items():
            assert abs(median([brands[b][fuel] for b in selected])/cap-1) <= D('.005'), 'MD multi-network median differs from cap by >0.5%'
            for prices in brands.values():
                if fuel in prices:
                    assert cap*D('.90') <= prices[fuel] <= cap*D('1.005')


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
    counts = current.pop('_station_counts', {})
    current['brands'] = reject_isolated_jumps(current['brands'], prior, today)
    current['average'] = average(current['brands'], country, counts)
    validate_day(current, country, station_counts=counts)
    assert current['day'] == today.isoformat(), 'collector day differs from local collection day'
    SELECTIONS[country] = {'selected':select_networks(current['brands'],country,counts),
                           'stationCounts':counts, 'countsScope':'active national registry' if country=='MD' else 'observed three-city sample'}
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
    SELECTIONS.clear()
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
    errors = freshness_errors(countries, now)
    if errors:
        if report_path:
            report_path.parent.mkdir(parents=True, exist_ok=True)
            report_path.write_text(json.dumps({'countries':status, 'warnings':WARNINGS,
                'requests':REQUESTS, 'freshnessErrors':errors, 'selections':SELECTIONS, 'changedFiles':[], 'privateFallbackEnabled':False,
                'tlsVerification':True}, ensure_ascii=False, indent=2)+'\n')
        raise RuntimeError('Stale or missing fuel feed. ' + ' | '.join(errors))
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
              'latestBytes':len(raw),'warnings':WARNINGS,'requests':REQUESTS,'selections':SELECTIONS,
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
