# aurum_lead_mapper_app.py
# Aurum Lead Mapper — v1.3.3
# - OSM Overpass POI (alto volume) com mirrors + retry
# - Google Places: Nearby (types) + Text Search (keywords) + Details (telefone/site)
# - Diagnóstico de fontes, limpar cache, orçamento de tempo ajustável
# - Telhado via Overpass (heurísticas largest/nearest/hybrid)
# - CRM leve (salvar/mesclar/exportar leads)
# - Aba "Maiores Telhados" com persistência (sem “pisca e some”)

import os, math, time, json
from typing import List, Dict
import pandas as pd
import requests
import streamlit as st
from shapely.geometry import Polygon, MultiPolygon, Point
from pyproj import Transformer
import folium
from folium.plugins import HeatMap
from streamlit_folium import st_folium
from dotenv import load_dotenv
from collections import Counter
import psycopg2

# ================== Setup básico / Tema ==================
load_dotenv()
st.set_page_config(page_title="Aurum Lead Mapper", layout="wide")

st.markdown("""
<style>
.stApp { background:#001f3f; color:#fff; }
.stApp h1, .stApp h2, .stApp h3, .stApp p, .stApp label { color:#fff; }
.stSidebar { background:#003366; }
.stButton>button { background:#FF8C00; color:#fff; border:0; }
a { color:#FFCC66; }
[data-testid="stMetricDelta"] svg { fill:#FFCC66; }
</style>
""", unsafe_allow_html=True)

# ================== Constantes / Config ==================
GOOGLE_PLACES_API_KEY = (os.getenv("GOOGLE_PLACES_API_KEY") or "").strip()
HEADERS = {"User-Agent": "AurumLeadMapper/1.3.3"}

REQUEST_TIMEOUT_S = 12
DETAILS_TIMEOUT_S = 8
SLEEP_BETWEEN_QUERIES = 0.25

AUTH_USERS = {
    "aurum": "STC",
    "MarcoBoer": "123456",
}

NEON_DB_URL = os.getenv(
    "NEON_DB_URL",
    "postgresql://neondb_owner:npg_1U6NcWKILQTS@ep-round-mode-ahr5mg6o-pooler.c-3.us-east-1.aws.neon.tech/neondb?sslmode=require&channel_binding=require",
)

# ---------- Catálogos ----------
CATEGORIES_PRESETS = {
    "Supermercados / Atacarejos": [
        "supermarket","supermercado","hypermarket","hipermercado","grocery","mercearia",
        "cash and carry","atacarejo","atacado","wholesale club","wholesale","club atacadista",
        "center grocery","food wholesaler","food distributor",
        "Atacadão","Assaí","Makro","Sam's Club","Carrefour","Carrefour Bairro","Pão de Açúcar",
        "Extra","Dia","Big","Guanabara","Rede Economia","Mundial","Prezunic","Supermarket",
        "Multimarket","SuperPrix","Super Rede","Costazul","Vianense","Inter Supermercados",
        "Princesa Supermercados","Real Supermercados","Santa Marta","Unidos Supermercados",
        "centro de compras","centro de abastecimento","atacado de alimentos"
    ],
    "Galpões / Logística / Fábricas": [
        "warehouse","galpão","galpao","logistics center","fulfillment center","distribution center",
        "CD","centro de distribuição","armazém","armazem","almoxarifado","porto seco",
        "depósito","deposito","retroárea","ZUP","ZPE","condomínio logístico","park logístico",
        "industrial park","parque industrial","distrito industrial","plataforma logística",
        "transportadora","courier","cross-docking","last mile hub",
        "factory","fábrica","industria","manufatura","planta industrial","offshore base"
    ],
    "Shoppings / Centros Comerciais": [
        "shopping","shopping center","mall","plaza","boulevard","strip mall","centro comercial",
        "open mall","lifestyle center","outlet","outlet premium",
        "Plaza Niterói","Partage","ParkShopping","Shopping Boulevard","Shopping Nova América",
        "Via Parque","Bangu Shopping","Shopping Rio Sul","Shopping Leblon"
    ],
    "Hotéis / Resorts / Pousadas": [
        "hotel","resort","pousada","hostel","inn","spa resort","eco resort","business hotel",
        "convention hotel","conference center","hotel fazenda",
        "Hilton","Accor","Ibis","Mercure","Novotel","Bourbon","Windsor",
        "Radisson","Sheraton","Marriott","Hampton","Best Western"
    ],
    "Condomínios Comerciais": [
        "business park","office park","commercial condominium","condomínio empresarial",
        "centro empresarial","complexo empresarial","edifício comercial","torre comercial",
        "centro executivo","coworking","multioffice","tech park","polo tecnológico"
    ],
    "Postos / Eletropostos": [
        "posto","posto de gasolina","posto de combustíveis","gas station","fuel station",
        "GNV","diesel","etanol","Ipiranga","BR","Shell","Raízen","ALE",
        "eletroposto","charging station","EV charging","carregador veicular",
        "carregamento rápido","fast charger","DC fast","Shell Recharge","Zletric","Ultracharge"
    ],
    "Escolas / Universidades / Prefeituras": [
        "school","escola","colegio","colégio","universidade","campus","faculdade",
        "instituto federal","CEFET","IFRJ","UFF","UFRJ","UERJ","PUC",
        "prefeitura","secretaria","câmara municipal","autarquia","hospital universitário",
        "centro educacional","sede administrativa","base operacional"
    ],
    "Hospitais / Clínicas / Saúde": [
        "hospital","maternidade","UPA","pronto socorro","clínica","policlínica",
        "laboratório","hemodiálise","oncologia","centro médico","complexo hospitalar",
        "Rede D'Or","Unimed","Samaritano","Americas Medical","Lifecenter"
    ],
    "Data Centers / TI Crítica": [
        "data center","datacenter","teleporto","pops","noc","edge datacenter",
        "telecom hub","central telefônica","central de comutação","subestação de TI"
    ],
    "Frigoríficos / Câmaras Frias": [
        "frigorífico","frigorifico","câmara fria","camara fria","centro de distribuição refrigerado",
        "cold storage","food cold chain","abatedouro"
    ],
    "Aeroportos / Portos / Terminais": [
        "aeroporto","aeródromo","terminal de cargas","terminal portuário","porto",
        "pátio regulador","retroporto","estação aduaneira","porto seco"
    ],
    "Residencial / Indefinido": [],
}
CATEGORY_WEIGHTS = {
    "Supermercados / Atacarejos": 1.0, "Galpões / Logística / Fábricas": 1.0,
    "Shoppings / Centros Comerciais": 0.9, "Hotéis / Resorts / Pousadas": 0.8,
    "Condomínios Comerciais": 0.8, "Postos / Eletropostos": 0.7,
    "Escolas / Universidades / Prefeituras": 0.8,
    "Hospitais / Clínicas / Saúde": 0.9, "Data Centers / TI Crítica": 1.0,
    "Frigoríficos / Câmaras Frias": 0.9, "Aeroportos / Portos / Terminais": 0.8,
    "Residencial / Indefinido": 0.4
}
GOOGLE_TYPES_BY_CATEGORY = {
    "Supermercados / Atacarejos": ["supermarket", "grocery_or_supermarket"],
    "Galpões / Logística / Fábricas": [],
    "Shoppings / Centros Comerciais": ["shopping_mall"],
    "Hotéis / Resorts / Pousadas": ["lodging"],
    "Condomínios Comerciais": ["establishment"],
    "Postos / Eletropostos": ["gas_station"],
    "Escolas / Universidades / Prefeituras": ["school", "university"],
    "Hospitais / Clínicas / Saúde": ["hospital"],
    "Data Centers / TI Crítica": [],
    "Frigoríficos / Câmaras Frias": [],
    "Aeroportos / Portos / Terminais": ["airport"],
}
OSM_TAGS_BY_CATEGORY = {
    "Supermercados / Atacarejos": [
        ('shop', 'supermarket'), ('shop','wholesale'), ('shop','hypermarket'),
        ('amenity','marketplace'), ('shop','convenience')
    ],
    "Galpões / Logística / Fábricas": [
        ('building','warehouse'), ('landuse','industrial'), ('building','industrial'), ('landuse','commercial')
    ],
    "Shoppings / Centros Comerciais": [
        ('shop','mall'), ('amenity','marketplace')
    ],
    "Hotéis / Resorts / Pousadas": [
        ('tourism','hotel'), ('tourism','hostel'), ('tourism','guest_house'), ('tourism','resort')
    ],
    "Condomínios Comerciais": [
        ('building','commercial'), ('office','company'), ('landuse','commercial'),
        ('office','administrative'), ('office','commercial')
    ],
    "Postos / Eletropostos": [
        ('amenity','fuel'), ('amenity','charging_station')
    ],
    "Escolas / Universidades / Prefeituras": [
        ('amenity','school'), ('amenity','university'), ('amenity','college'), ('office','government')
    ],
    "Hospitais / Clínicas / Saúde": [
        ('amenity','hospital'), ('amenity','clinic'), ('amenity','doctors')
    ],
    "Data Centers / TI Crítica": [
        ('man_made','works')
    ],
    "Frigoríficos / Câmaras Frias": [
        ('industrial','food_processing'), ('building','industrial')
    ],
    "Aeroportos / Portos / Terminais": [
        ('aeroway','aerodrome'), ('aeroway','terminal'), ('amenity','ferry_terminal'), ('landuse','harbour')
    ],
}

# ================== Estado ==================
if "df" not in st.session_state: st.session_state.df = None
if "last_params" not in st.session_state: st.session_state.last_params = None
if "saved_leads" not in st.session_state: st.session_state.saved_leads = None
if "auth_user" not in st.session_state: st.session_state.auth_user = None
if "heatmap_df" not in st.session_state: st.session_state.heatmap_df = None
# Persistência da aba Maiores Telhados
if "big_roofs_df" not in st.session_state: st.session_state.big_roofs_df = None
if "big_roofs_center" not in st.session_state: st.session_state.big_roofs_center = None  # {lat, lon, name}
if "big_roofs_params" not in st.session_state: st.session_state.big_roofs_params = None  # {radius_km, min_area, topn}

# ================== Login ==================
def render_login():
    st.title("🔐 Aurum Lead Mapper")
    st.caption("Entre com seu usuário para continuar.")
    with st.form("login_form"):
        username = st.text_input("Usuário")
        password = st.text_input("Senha", type="password")
        submit = st.form_submit_button("Entrar")
    if submit:
        if AUTH_USERS.get(username) == password:
            st.session_state.auth_user = username
            try:
                st.session_state.saved_leads = load_leads_from_neon(username)
            except Exception as e:
                st.warning(f"Falha ao carregar leads do Neon: {e}")
            st.success(f"Bem-vindo, {username}!")
        else:
            st.error("Usuário ou senha inválidos.")

# ================== Utilitários geométricos ==================
def get_utm_epsg(lon: float, lat: float) -> int:
    zone = int((lon + 180) // 6) + 1
    return int(f"327{zone:02d}" if lat < 0 else f"326{zone:02d}")

def project_area_m2(geom) -> float:
    try:
        centroid = geom.centroid
        epsg = get_utm_epsg(centroid.x, centroid.y)
        tr = Transformer.from_crs("EPSG:4326", f"EPSG:{epsg}", always_xy=True)
        def _p(coords): return [tr.transform(x, y) for (x, y) in coords]
        if isinstance(geom, Polygon):
            return abs(Polygon(_p(list(geom.exterior.coords)),
                              [_p(list(r.coords)) for r in geom.interiors]).area)
        elif isinstance(geom, MultiPolygon):
            return sum(project_area_m2(p) for p in geom.geoms)
    except Exception:
        return 0.0
    return 0.0

def estimate_kwp(area_m2: float, area_per_kwp: float = 6.0, coverage_ratio: float = 0.6) -> float:
    usable = max(area_m2, 0.0) * coverage_ratio
    return round(usable / (area_per_kwp if area_per_kwp > 0 else 6.0), 2)

def estimate_generation_kwh_year(kwp: float, specific_yield: float = 1500.0) -> float:
    return round(max(kwp, 0.0) * specific_yield, 0)

def haversine_km(lat1, lon1, lat2, lon2):
    R = 6371.0
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1); dl = math.radians(lon2 - lon1)
    a = math.sin(dphi/2)**2 + math.cos(phi1)*math.cos(phi2)*math.sin(dl/2)**2
    return 2 * R * math.asin(math.sqrt(a))

def aurum_score(category: str, area_m2: float, distance_km: float, base_weight: float = 1.0) -> float:
    w_cat = CATEGORY_WEIGHTS.get(category, 0.7)
    area_score = min(area_m2 / 500.0, 1.0)
    dist_score = 1.0 / (1.0 + (distance_km/20.0))
    return round(100.0 * w_cat * area_score * dist_score * base_weight, 1)

# ================== Overpass helpers (mirrors + retry) ==================
OVERPASS_ENDPOINTS = [
    "https://overpass-api.de/api/interpreter",
    "https://overpass.kumi.systems/api/interpreter",
    "https://overpass.openstreetmap.ru/api/interpreter",
    "https://z.overpass-api.de/api/interpreter",
]

def _overpass_call(query: str, timeout_s: int = REQUEST_TIMEOUT_S):
    last_err = None
    for url in OVERPASS_ENDPOINTS:
        try:
            r = requests.post(url, data=query.encode("utf-8"),
                              headers={"Content-Type":"text/plain"},
                              timeout=timeout_s)
            if r.status_code == 200:
                return r.json()
        except Exception as e:
            last_err = e
            time.sleep(0.5)
    if last_err:
        raise last_err
    return {"elements": []}

@st.cache_data(ttl=300, show_spinner=False)
def overpass_buildings_around(lat: float, lon: float, radius_m: int = 200) -> List[Polygon]:
    query = f"""
    [out:json][timeout:25];
    ( way["building"](around:{radius_m},{lat},{lon});
      relation["building"](around:{radius_m},{lat},{lon}); );
    out body; >; out skel qt;
    """
    polys = []
    try:
        data = _overpass_call(query, timeout_s=max(REQUEST_TIMEOUT_S, 20))
        elems = data.get("elements", [])
        nodes = {e["id"]:(e["lon"], e["lat"]) for e in elems if e["type"]=="node"}
        for e in elems:
            if e["type"]=="way" and "nodes" in e:
                coords = [nodes.get(n) for n in e["nodes"] if n in nodes]
                if coords and len(coords) >= 3:
                    try:
                        poly = Polygon(coords)
                        if poly.is_valid and poly.area > 0: polys.append(poly)
                    except Exception:
                        pass
    except Exception:
        pass
    return polys

@st.cache_data(ttl=600, show_spinner=False)
def overpass_buildings_geom_region(lat: float, lon: float, radius_m: int, limit: int = 4000) -> List[Polygon]:
    query = f"""
    [out:json][timeout:90];
    ( way["building"](around:{radius_m},{lat},{lon});
      relation["building"](around:{radius_m},{lat},{lon}); );
    out tags geom {limit};
    """
    try:
        data = _overpass_call(query, timeout_s=max(REQUEST_TIMEOUT_S*3, 30))
    except Exception:
        data = {"elements": []}
    polys: List[Polygon] = []
    for el in data.get("elements", []):
        geom = el.get("geometry")
        if not geom or len(geom) < 3: continue
        try:
            coords = [(pt["lon"], pt["lat"]) for pt in geom]
            poly = Polygon(coords)
            if poly.is_valid and poly.area > 0: polys.append(poly)
        except Exception:
            continue
    return polys

def overpass_poi_search(lat: float, lon: float, radius_m: int, category: str, limit: int | None = None) -> List[Dict]:
    tags = OSM_TAGS_BY_CATEGORY.get(category, [])
    if not tags: return []
    filters = " ".join([
        f'node["{k}"="{v}"](around:{radius_m},{lat},{lon});'
        f'way["{k}"="{v}"](around:{radius_m},{lat},{lon});'
        f'relation["{k}"="{v}"](around:{radius_m},{lat},{lon});'
        for k, v in tags
    ])
    out_clause = f"out center {limit};" if limit else "out center;"
    query = f"""
    [out:json][timeout:30];
    ( {filters} );
    {out_clause}
    """
    try:
        data = _overpass_call(query, timeout_s=max(REQUEST_TIMEOUT_S, 20))
    except Exception:
        return []
    out = []
    for el in data.get("elements", []):
        if el.get("type") in ("node","way","relation"):
            tg = el.get("tags", {}) or {}
            name = tg.get("name") or str(el.get("id"))
            phone = tg.get("contact:phone") or tg.get("phone")
            website = tg.get("contact:website") or tg.get("website")
            email = tg.get("contact:email") or tg.get("email")
            if el.get("type") == "node":
                latc, lonc = el.get("lat"), el.get("lon")
            else:
                center = el.get("center") or {}
                latc, lonc = center.get("lat"), center.get("lon")
            if latc is None or lonc is None: continue
            out.append({
                "name": name, "address": None, "lat": latc, "lon": lonc,
                "source": "osm_overpass", "osm_id": el.get("id"),
                "class": None, "type": None,
                "phone": phone, "website": website, "email": email,
                "category": category
            })
    return out[:limit] if limit else out

@st.cache_data(ttl=600, show_spinner=False)
def overpass_buildings_with_tags_region(lat: float, lon: float, radius_m: int, limit: int = 4000) -> List[Dict]:
    query = f"""
    [out:json][timeout:90];
    ( way["building"](around:{radius_m},{lat},{lon});
      relation["building"](around:{radius_m},{lat},{lon}); );
    out center tags {limit};
    """
    try:
        data = _overpass_call(query, timeout_s=max(REQUEST_TIMEOUT_S*3, 30))
    except Exception:
        return []
    out = []
    for el in data.get("elements", []):
        center = el.get("center") or {}
        latc, lonc = center.get("lat"), center.get("lon")
        if latc is None or lonc is None:
            continue
        tags = el.get("tags", {}) or {}
        out.append({
            "id": el.get("id"),
            "lat": latc,
            "lon": lonc,
            "tags": tags,
        })
    return out[:limit]

def classify_osm_tags(tags: Dict) -> Dict:
    if not tags:
        return {"category": "Residencial / Indefinido", "detail": None}

    shop = tags.get("shop")
    amenity = tags.get("amenity")
    tourism = tags.get("tourism")
    office = tags.get("office")
    industrial = tags.get("industrial")
    landuse = tags.get("landuse")
    building = tags.get("building")
    aeroway = tags.get("aeroway")
    man_made = tags.get("man_made")

    if shop in {"supermarket", "wholesale", "hypermarket", "convenience", "grocery"} or amenity == "marketplace":
        return {"category": "Supermercados / Atacarejos", "detail": shop or amenity}
    if shop == "mall" or amenity == "marketplace":
        return {"category": "Shoppings / Centros Comerciais", "detail": shop or amenity}
    if tourism in {"hotel", "hostel", "guest_house", "resort"}:
        return {"category": "Hotéis / Resorts / Pousadas", "detail": tourism}
    if amenity in {"fuel", "charging_station"}:
        return {"category": "Postos / Eletropostos", "detail": amenity}
    if amenity in {"school", "university", "college"} or office == "government":
        return {"category": "Escolas / Universidades / Prefeituras", "detail": amenity or office}
    if amenity in {"hospital", "clinic", "doctors"}:
        return {"category": "Hospitais / Clínicas / Saúde", "detail": amenity}
    if man_made == "works":
        return {"category": "Data Centers / TI Crítica", "detail": man_made}
    if industrial == "food_processing":
        return {"category": "Frigoríficos / Câmaras Frias", "detail": industrial}
    if aeroway in {"aerodrome", "terminal"} or amenity == "ferry_terminal" or landuse == "harbour":
        return {"category": "Aeroportos / Portos / Terminais", "detail": aeroway or amenity or landuse}
    if building in {"warehouse", "industrial"} or landuse in {"industrial", "commercial"}:
        return {"category": "Galpões / Logística / Fábricas", "detail": building or landuse}
    if building in {"commercial", "office"} or office in {"company", "administrative", "commercial"}:
        return {"category": "Condomínios Comerciais", "detail": building or office}
    if building in {"house", "residential", "apartments", "detached", "semidetached_house", "terrace"}:
        return {"category": "Residencial / Indefinido", "detail": building}

    return {"category": "Residencial / Indefinido", "detail": building or amenity or shop or office}

@st.cache_data(ttl=24*3600, show_spinner=False)
def reverse_geocode_bairro(lat: float, lon: float) -> str:
    url = "https://nominatim.openstreetmap.org/reverse"
    params = {
        "format": "jsonv2",
        "lat": lat,
        "lon": lon,
        "zoom": 18,
        "addressdetails": 1,
    }
    try:
        resp = requests.get(url, params=params, headers=HEADERS, timeout=REQUEST_TIMEOUT_S)
        data = resp.json()
    except Exception:
        return "—"
    address = data.get("address", {}) or {}
    return (
        address.get("suburb")
        or address.get("neighbourhood")
        or address.get("city_district")
        or address.get("quarter")
        or address.get("village")
        or "—"
    )

def ensure_neon_table(conn) -> None:
    with conn.cursor() as cur:
        cur.execute(
            """
            CREATE TABLE IF NOT EXISTS aurum_leads (
                id SERIAL PRIMARY KEY,
                usuario TEXT,
                nome TEXT,
                telefone TEXT,
                site TEXT,
                email TEXT,
                endereco TEXT,
                categoria TEXT,
                fonte TEXT,
                rating DOUBLE PRECISION,
                reviews INTEGER,
                maps_url TEXT,
                latitude DOUBLE PRECISION,
                longitude DOUBLE PRECISION,
                area_telhado_m2 DOUBLE PRECISION,
                potencia_kwp DOUBLE PRECISION,
                geracao_kwh DOUBLE PRECISION,
                distancia_km DOUBLE PRECISION,
                aurum_score DOUBLE PRECISION,
                campanha TEXT,
                responsavel TEXT,
                estagio TEXT,
                obs TEXT,
                salvo_em TIMESTAMP
            );
            """
        )
        cur.execute(
            """
            ALTER TABLE aurum_leads
            ADD COLUMN IF NOT EXISTS usuario TEXT;
            """
        )
    conn.commit()

def save_leads_to_neon(df: pd.DataFrame, usuario: str | None = None) -> None:
    if df.empty:
        return
    if not usuario:
        usuario = st.session_state.get("auth_user")
    if not usuario:
        raise ValueError("Usuário não informado para salvar no Neon.")
    with psycopg2.connect(NEON_DB_URL) as conn:
        ensure_neon_table(conn)
        with conn.cursor() as cur:
            insert_sql = """
                INSERT INTO aurum_leads (
                    usuario, nome, telefone, site, email, endereco, categoria, fonte, rating, reviews,
                    maps_url, latitude, longitude, area_telhado_m2, potencia_kwp, geracao_kwh,
                    distancia_km, aurum_score, campanha, responsavel, estagio, obs, salvo_em
                ) VALUES (
                    %(usuario)s, %(nome)s, %(telefone)s, %(site)s, %(email)s, %(endereco)s, %(categoria)s,
                    %(fonte)s, %(rating)s, %(reviews)s, %(maps_url)s, %(latitude)s,
                    %(longitude)s, %(area_telhado_m2)s, %(potencia_kwp)s, %(geracao_kwh)s,
                    %(distancia_km)s, %(aurum_score)s, %(campanha)s, %(responsavel)s,
                    %(estagio)s, %(obs)s, %(salvo_em)s
                );
            """
            records = []
            for _, row in df.iterrows():
                records.append(
                    {
                        "usuario": usuario,
                        "nome": row.get("Nome"),
                        "telefone": row.get("Telefone"),
                        "site": row.get("Site"),
                        "email": row.get("E-mail"),
                        "endereco": row.get("Endereço"),
                        "categoria": row.get("Categoria"),
                        "fonte": row.get("Fonte"),
                        "rating": row.get("Rating"),
                        "reviews": row.get("Reviews"),
                        "maps_url": row.get("Maps URL"),
                        "latitude": row.get("Latitude"),
                        "longitude": row.get("Longitude"),
                        "area_telhado_m2": row.get("Área telhado (m²)"),
                        "potencia_kwp": row.get("Potência estimada (kWp)"),
                        "geracao_kwh": row.get("Geração anual (kWh)"),
                        "distancia_km": row.get("Distância da base (km)"),
                        "aurum_score": row.get("Aurum Score"),
                        "campanha": row.get("Campanha"),
                        "responsavel": row.get("Responsável"),
                        "estagio": row.get("Estágio"),
                        "obs": row.get("Obs"),
                        "salvo_em": row.get("Salvo_em"),
                    }
                )
            cur.executemany(insert_sql, records)
        conn.commit()

def load_leads_from_neon(usuario: str) -> pd.DataFrame:
    with psycopg2.connect(NEON_DB_URL) as conn:
        ensure_neon_table(conn)
        query = """
            SELECT
                nome AS "Nome",
                telefone AS "Telefone",
                site AS "Site",
                email AS "E-mail",
                endereco AS "Endereço",
                categoria AS "Categoria",
                fonte AS "Fonte",
                rating AS "Rating",
                reviews AS "Reviews",
                maps_url AS "Maps URL",
                latitude AS "Latitude",
                longitude AS "Longitude",
                area_telhado_m2 AS "Área telhado (m²)",
                potencia_kwp AS "Potência estimada (kWp)",
                geracao_kwh AS "Geração anual (kWh)",
                distancia_km AS "Distância da base (km)",
                aurum_score AS "Aurum Score",
                campanha AS "Campanha",
                responsavel AS "Responsável",
                estagio AS "Estágio",
                obs AS "Obs",
                salvo_em AS "Salvo_em"
            FROM aurum_leads
            WHERE usuario = %s
            ORDER BY salvo_em DESC;
        """
        return pd.read_sql(query, conn, params=(usuario,))

if not st.session_state.auth_user:
    render_login()
    st.stop()
elif st.session_state.saved_leads is None:
    try:
        st.session_state.saved_leads = load_leads_from_neon(st.session_state.auth_user)
    except Exception as e:
        st.warning(f"Falha ao carregar leads do Neon: {e}")

# ================== Telhado (heurística) ==================
def pick_roof_polygon_nearest(polygons, poi_lat, poi_lon):
    poi = Point(poi_lon, poi_lat)
    def dist(poly): c = poly.centroid; return haversine_km(poi.y, poi.x, c.y, c.x)
    return min(polygons, key=dist)

def pick_roof_polygon_hybrid(polygons, poi_lat, poi_lon, w_area=0.6, w_near=0.4):
    areas = [project_area_m2(p) for p in polygons]; max_a = max(areas) or 1.0
    dists = [haversine_km(poi_lat, poi_lon, p.centroid.y, p.centroid.x) for p in polygons]; max_d = max(dists) or 1.0
    scores = []
    for a, d in zip(areas, dists):
        area_score = a / max_a
        near_score = 1.0 - (d / max_d)
        scores.append(w_area*area_score + w_near*near_score)
    return polygons[scores.index(max(scores))]

def estimate_rooftop_area_m2(polygons, poi_lat=None, poi_lon=None, mode="largest"):
    if not polygons: return 0.0
    if mode == "nearest" and poi_lat is not None:
        chosen = pick_roof_polygon_nearest(polygons, poi_lat, poi_lon)
    elif mode == "hybrid" and poi_lat is not None:
        chosen = pick_roof_polygon_hybrid(polygons, poi_lat, poi_lon)
    else:
        chosen = max(polygons, key=lambda p: project_area_m2(p))
    return project_area_m2(chosen) if chosen is not None else 0.0

# ================== Geocodificação e Google APIs ==================
@st.cache_data(ttl=86400, show_spinner=False)
def geocode_location(location_name: str, api_key: str = "") -> Dict[str, float]:
    name = (location_name or "").strip()
    if "," in name:
        try:
            a, b = [float(x.strip()) for x in name.split(",")]
            return {"lat": a, "lon": b}
        except Exception:
            pass
    if api_key:
        try:
            url = "https://maps.googleapis.com/maps/api/geocode/json"
            params = {"address": name, "key": api_key, "language": "pt-BR"}
            r = requests.get(url, params=params, headers=HEADERS, timeout=REQUEST_TIMEOUT_S)
            data = r.json()
            if data.get("results"):
                loc = data["results"][0]["geometry"]["location"]
                return {"lat": loc["lat"], "lon": loc["lng"]}
        except Exception:
            pass
    try:
        url = "https://nominatim.openstreetmap.org/search"
        params = {"q": name, "format": "json", "limit": 1}
        r = requests.get(url, params=params, headers=HEADERS, timeout=REQUEST_TIMEOUT_S)
        data = r.json()
        if data:
            return {"lat": float(data[0]["lat"]), "lon": float(data[0]["lon"])}
    except Exception:
        pass
    return {"lat": -22.9, "lon": -43.2}

@st.cache_data(ttl=300, show_spinner=False)
def google_places_text_search(q: str, lat: float, lon: float, radius_m: int, max_results: int, api_key: str) -> List[Dict]:
    if not api_key: return []
    url = "https://maps.googleapis.com/maps/api/place/textsearch/json"
    params = {"query": q, "location": f"{lat},{lon}", "radius": radius_m, "key": api_key, "language": "pt-BR"}
    res = []
    try:
        while True:
            r = requests.get(url, params=params, headers=HEADERS, timeout=REQUEST_TIMEOUT_S)
            data = r.json(); res += data.get("results", [])
            tok = data.get("next_page_token")
            if not tok or len(res) >= max_results: break
            time.sleep(2); params["pagetoken"] = tok
    except Exception:
        pass
    out = []
    for it in res[:max_results]:
        loc = it.get("geometry", {}).get("location", {})
        out.append({
            "name": it.get("name"),
            "address": it.get("formatted_address"),
            "lat": loc.get("lat"), "lon": loc.get("lng"),
            "source": "google_text", "place_id": it.get("place_id"),
            "rating": it.get("rating"), "reviews": it.get("user_ratings_total"),
            "types": it.get("types", [])
        })
    return out

@st.cache_data(ttl=300, show_spinner=False)
def google_places_nearby(lat: float, lon: float, radius_m: int, gtype: str, max_results: int, api_key: str) -> List[Dict]:
    if not api_key or not gtype: return []
    url = "https://maps.googleapis.com/maps/api/place/nearbysearch/json"
    params = {"location": f"{lat},{lon}", "radius": radius_m, "type": gtype, "key": api_key, "language":"pt-BR"}
    res = []
    try:
        while True:
            r = requests.get(url, params=params, headers=HEADERS, timeout=REQUEST_TIMEOUT_S)
            data = r.json(); res += data.get("results", [])
            tok = data.get("next_page_token")
            if not tok or len(res) >= max_results: break
            time.sleep(2); params["pagetoken"] = tok
    except Exception:
        pass
    out = []
    for it in res[:max_results]:
        loc = it.get("geometry", {}).get("location", {})
        out.append({
            "name": it.get("name"),
            "address": it.get("vicinity"),
            "lat": loc.get("lat"), "lon": loc.get("lng"),
            "source": "google_nearby", "place_id": it.get("place_id"),
            "rating": it.get("rating"), "reviews": it.get("user_ratings_total"),
            "types": it.get("types", [])
        })
    return out

@st.cache_data(ttl=300, show_spinner=False)
def google_place_details(place_id: str, api_key: str) -> Dict:
    if not api_key or not place_id: return {}
    url = "https://maps.googleapis.com/maps/api/place/details/json"
    fields = ",".join([
        "international_phone_number","formatted_phone_number","website",
        "opening_hours","business_status","url","plus_code"
    ])
    params = {"place_id": place_id, "key": api_key, "language":"pt-BR", "fields": fields}
    try:
        r = requests.get(url, params=params, headers=HEADERS, timeout=DETAILS_TIMEOUT_S)
        res = r.json().get("result", {})
        phone = res.get("international_phone_number") or res.get("formatted_phone_number")
        website = res.get("website")
        hours = None
        if isinstance(res.get("opening_hours", {}).get("weekday_text"), list):
            hours = "; ".join(res["opening_hours"]["weekday_text"])
        return {
            "phone": phone, "website": website, "opening_hours": hours,
            "status": res.get("business_status"), "maps_url": res.get("url"),
            "plus_code": res.get("plus_code", {}).get("global_code")
        }
    except Exception:
        return {}

# ================== Título / Sidebar ==================
st.title("⚡ Aurum Lead Mapper — prospecção geointeligente")
st.caption("Overpass POI • Google Nearby + Text • Details • Dashboard • CRM • Maiores Telhados")

with st.sidebar:
    st.caption(f"Usuário: **{st.session_state.auth_user}**")
    if st.button("Sair"):
        st.session_state.auth_user = None
        st.session_state.heatmap_df = None
        st.session_state.saved_leads = None
        st.rerun()

    st.header("🔧 Configurações")
    if st.button("🧹 Limpar cache (dados)"):
        st.cache_data.clear()
        st.success("Cache limpo. Rode novamente.")

    with st.form("controls"):
        gkey = st.text_input("Google Places API Key", value=GOOGLE_PLACES_API_KEY, type="password")
        enrich_details = st.checkbox("Enriquecer com telefone/site (Google Details)", value=bool(gkey))
        supplement_nominatim = st.checkbox("Suplemento Nominatim (texto livre)", value=False,
                                           help="Pode trazer extra, mas menos preciso que Overpass.")

        st.markdown("**Região alvo (texto livre ou 'lat,lon')**")
        custom_location = st.text_input("Local (ex.: 'Niterói' ou '-22.9, -43.1')", "Niterói")
        radius_km = st.slider("Raio de busca (km)", 5, 60, 20, 1)

        st.markdown("**Parâmetros FV**")
        area_per_kwp = st.number_input("m² por kWp", 4.0, 10.0, 6.0, 0.1)
        coverage_ratio = st.slider("Fator de cobertura do telhado", 0.3, 0.9, 0.6, 0.05)
        specific_yield = st.number_input("Specific yield (kWh/kWp·ano)", 1100.0, 1900.0, 1500.0, 10.0)

        st.markdown("**Base operacional**")
        base_lat = st.number_input("Base lat", value=-22.8832, format="%.6f")
        base_lon = st.number_input("Base lon", value=-43.1034, format="%.6f")

        st.markdown("**Busca**")
        collect_mode = st.selectbox(
            "Modo de coleta",
            ["Categoria / palavras-chave", "Cobertura total (OSM: todos edifícios)"]
        )
        category = st.selectbox("Categoria", list(CATEGORIES_PRESETS.keys()))
        keywords_default = ", ".join(CATEGORIES_PRESETS[category])
        keywords = st.text_area("Palavras-chave (vírgulas)", value=keywords_default, height=80)
        max_results = st.slider("Máximo de leads (parar quando atingir)", 50, 5000, 500, 50)
        use_google = st.checkbox("Usar Google Places (requer API key)", value=bool(gkey))
        use_osm = st.checkbox("Usar OSM Overpass POI", value=True)

        st.markdown("**Heurística do telhado (Overpass)**")
        roof_mode = st.selectbox("Escolha", ["largest","nearest","hybrid"])

        st.markdown("**Depuração / Performance**")
        fast_mode = st.checkbox("Modo Rápido (debug)", value=False,
                                help="Limita resultados e desativa Details para evitar travar.")
        overpass_enable = st.checkbox("Usar Overpass p/ telhados (OSM)", value=True)
        per_kw_limit = st.slider("Limite por palavra (p/ fonte)", 5, 60, 40, 5)
        overpass_radius_m = st.slider("Raio Overpass telhado (m)", 50, 400, 220, 10)

        run_btn = st.form_submit_button("🚀 Executar mapeamento")

# ================== Execução principal ==================
if run_btn:
    status = st.status("Iniciando busca…", expanded=True)
    status.update(label="Geocodificando região alvo…", state="running")

    target = geocode_location(custom_location, gkey if use_google else "")
    lat0, lon0 = target["lat"], target["lon"]
    radius_m = int(radius_km * 1000)

    if collect_mode == "Cobertura total (OSM: todos edifícios)":
        use_google = False
        use_osm = True
        supplement_nominatim = False
        enrich_details = False

    if fast_mode:
        max_results = min(max_results, 60)
        enrich_details = False

    keys = [k.strip() for k in keywords.split(",") if k.strip()]
    per_kw = per_kw_limit
    seen, results = set(), []

    total_steps = max(1,
        (1 if use_osm else 0) +
        (len(GOOGLE_TYPES_BY_CATEGORY.get(category, [])) if (use_google and gkey) else 0) +
        (len(keys) if (use_google and gkey) else 0) +
        (1 if supplement_nominatim else 0)
    )
    prog = st.progress(0); steps_done = 0

    status.update(label="Coletando locais (OSM → Google)…", state="running")

    # 1) OSM primeiro (alto volume)
    if use_osm:
        try:
            if collect_mode == "Cobertura total (OSM: todos edifícios)":
                data = overpass_buildings_with_tags_region(lat0, lon0, radius_m, limit=max_results)
                for d in data:
                    if len(results) >= max_results:
                        break
                    tags = d.get("tags", {}) or {}
                    classification = classify_osm_tags(tags)
                    name = tags.get("name") or tags.get("addr:housename")
                    if not name:
                        name = "Residência" if classification["category"] == "Residencial / Indefinido" else f"Edificação {d.get('id')}"
                    k = (round(d["lat"], 6), round(d["lon"], 6), name)
                    if k not in seen:
                        seen.add(k)
                        results.append({
                            "name": name,
                            "address": tags.get("addr:full") or tags.get("addr:street"),
                            "lat": d["lat"],
                            "lon": d["lon"],
                            "source": "osm_buildings",
                            "osm_id": d.get("id"),
                            "class": tags.get("building"),
                            "type": classification.get("detail"),
                            "phone": tags.get("contact:phone") or tags.get("phone"),
                            "website": tags.get("contact:website") or tags.get("website"),
                            "email": tags.get("contact:email") or tags.get("email"),
                            "category": classification["category"],
                        })
            else:
                data = overpass_poi_search(lat0, lon0, radius_m, category, limit=max_results)
                for d in data:
                    if len(results) >= max_results:
                        break
                    k = (round(d["lat"],6), round(d["lon"],6), d["name"])
                    if k not in seen:
                        seen.add(k); results.append(d)
        except Exception as e:
            st.warning(f"OSM POI falhou: {e}")
        steps_done += 1; prog.progress(min(1.0, steps_done / total_steps))

    # 2) Google Nearby (types)
    if use_google and gkey:
        gtypes = GOOGLE_TYPES_BY_CATEGORY.get(category, [])
        for gtype in gtypes:
            if len(results) >= max_results:
                break
            try:
                data = google_places_nearby(lat0, lon0, radius_m, gtype=gtype,
                                            max_results=min(per_kw, max_results), api_key=gkey)
                for d in data:
                    if len(results) >= max_results:
                        break
                    k = (round(d["lat"],6), round(d["lon"],6), d["name"])
                    if k not in seen:
                        d["category"] = category; seen.add(k); results.append(d)
            except Exception as e:
                st.warning(f"Google Nearby falhou ({gtype}): {e}")
            steps_done += 1; prog.progress(min(1.0, steps_done / total_steps))
            time.sleep(SLEEP_BETWEEN_QUERIES)

    # 3) Google Text Search (keywords)
    if use_google and gkey and keys:
        for kw in keys:
            if len(results) >= max_results:
                break
            try:
                data = google_places_text_search(
                    f"{kw} near {custom_location}", lat0, lon0, radius_m,
                    max_results=min(per_kw, max_results), api_key=gkey
                )
                for d in data:
                    if len(results) >= max_results:
                        break
                    k = (round(d["lat"],6), round(d["lon"],6), d["name"])
                    if k not in seen:
                        d["category"] = category; seen.add(k); results.append(d)
            except Exception as e:
                st.warning(f"Google Text falhou ('{kw}'): {e}")
            steps_done += 1; prog.progress(min(1.0, steps_done / total_steps))
            time.sleep(SLEEP_BETWEEN_QUERIES)

    # 4) Suplemento Nominatim opcional (texto livre)
    def osm_nominatim_search(keyword: str, lat: float, lon: float, radius_m: int = 5000, limit: int = 50) -> List[Dict]:
        url = "https://nominatim.openstreetmap.org/search"
        params = {"q": keyword, "format": "jsonv2", "limit": limit, "lat": lat, "lon": lon, "radius": radius_m}
        try:
            resp = requests.get(url, params=params, headers=HEADERS, timeout=REQUEST_TIMEOUT_S)
            data = resp.json()
        except Exception:
            return []
        out = []
        for r in data:
            try:
                out.append({
                    "name": r.get("display_name", "").split(",")[0],
                    "address": r.get("display_name"),
                    "lat": float(r.get("lat")), "lon": float(r.get("lon")),
                    "source": "osm_nominatim", "category": category
                })
            except Exception:
                pass
        return out[:limit]

    if supplement_nominatim and len(results) < max_results:
        try:
            extra = osm_nominatim_search(category + " " + custom_location, lat0, lon0, radius_m, limit=50)
            for d in extra:
                if len(results) >= max_results:
                    break
                k = (round(d["lat"],6), round(d["lon"],6), d["name"])
                if k not in seen:
                    seen.add(k); results.append(d)
        except Exception as e:
            st.warning(f"Nominatim extra falhou: {e}")
        steps_done += 1; prog.progress(min(1.0, steps_done / total_steps))

    st.write(f"🧭 Locais encontrados (deduplicados): **{len(results)}**")

    # Diagnóstico de fontes
    src_count = Counter([r.get("source","?") for r in results])
    st.info("📊 Fontes: " + " | ".join([f"{k}:{v}" for k,v in src_count.items()]) if src_count else "📊 sem itens")

    status.update(label="Enriquecendo (telefone/site)…", state="running")

    # Details (opcional)
    if enrich_details and gkey:
        for i, item in enumerate(results[:min(150, len(results))]):
            if item.get("source","").startswith("google") and item.get("place_id"):
                det = google_place_details(item["place_id"], gkey)
                if det:
                    item["phone"] = det.get("phone")
                    item["website"] = det.get("website")
                    item["opening_hours"] = det.get("opening_hours")
                    item["status"] = det.get("status")
                    item["maps_url"] = det.get("maps_url")
                    item["plus_code"] = det.get("plus_code")
            if (i+1) % 12 == 0:
                st.caption(f"…details {i+1} / {min(150, len(results))}")
            time.sleep(0.08)

    status.update(label="Estimando telhados e kWp…", state="running")

    # Estimação FV + score
    rows = []
    for i, r in enumerate(results):
        lat, lon = r["lat"], r["lon"]
        buildings = []
        if overpass_enable:
            try:
                buildings = overpass_buildings_around(lat, lon, radius_m=overpass_radius_m)
            except Exception:
                buildings = []

        area_m2 = estimate_rooftop_area_m2(buildings, poi_lat=lat, poi_lon=lon, mode=roof_mode) if buildings else 0.0
        kwp = estimate_kwp(area_m2, area_per_kwp=area_per_kwp, coverage_ratio=coverage_ratio)
        gen = estimate_generation_kwh_year(kwp, specific_yield=specific_yield)
        dist = haversine_km(base_lat, base_lon, lat, lon)
        score = aurum_score(r.get("category", category), area_m2, dist)

        rows.append({
            "Nome": r.get("name"),
            "Telefone": r.get("phone"),
            "Site": r.get("website"),
            "E-mail": r.get("email"),
            "Endereço": r.get("address"),
            "Categoria": r.get("category", category),
            "Fonte": r.get("source"),
            "Rating": r.get("rating"),
            "Reviews": r.get("reviews"),
            "Maps URL": r.get("maps_url"),
            "Latitude": lat, "Longitude": lon,
            "Área telhado (m²)": round(area_m2,1),
            "Potência estimada (kWp)": round(kwp,1),
            "Geração anual (kWh)": round(gen,0),
            "Distância da base (km)": round(dist,1),
            "Aurum Score": score,
        })

        if (i+1) % 20 == 0:
            st.caption(f"Processados {i+1}/{len(results)}…")

        if len(rows) >= max_results:
            break

    if rows:
        df = pd.DataFrame(rows).sort_values(
            by=["Aurum Score","Potência estimada (kWp)","Área telhado (m²)"], ascending=False
        )
        st.session_state.df = df
        st.session_state.last_params = {
            "local": custom_location, "raio_km": radius_km, "categoria": category,
            "base_lat": base_lat, "base_lon": base_lon, "roof_mode": roof_mode
        }
        status.update(label="Concluído ✅", state="complete")
    else:
        status.update(label="Sem linhas para exibir (veja avisos acima).", state="error")

# ================== Abas (inclui Maiores Telhados) ==================
tab_dash, tab_map, tab_heatmap, tab_saved, tab_bigroofs = st.tabs(
    ["📊 Dashboard", "🗺️ Mapeamento atual", "🔥 Heatmap por Bairro", "📦 Leads salvos", "🏢 Maiores Telhados"]
)

# ---------- Dashboard ----------
with tab_dash:
    st.subheader("📊 Visão geral")
    df = st.session_state.df
    if df is None or df.empty:
        st.info("Sem resultados ainda. Execute um mapeamento.")
    else:
        for col, default in [
            ("Área telhado (m²)", 0.0),
            ("Potência estimada (kWp)", 0.0),
            ("Geração anual (kWh)", 0.0),
            ("Aurum Score", 0.0),
        ]:
            if col not in df.columns: df[col] = default

        c1, c2, c3, c4 = st.columns(4)
        with c1: st.metric("Leads encontrados", len(df))
        with c2: st.metric("kWp total", f"{df['Potência estimada (kWp)'].sum():,.0f}".replace(",","."))
        with c3: st.metric("Geração/ano (MWh)", f"{df['Geração anual (kWh)'].sum()/1000:,.1f}".replace(",","."))
        with c4: st.metric("Aurum Score médio", f"{df['Aurum Score'].mean():.1f}")

        st.markdown("**Por categoria**")
        by_cat = df.groupby("Categoria").agg(
            leads=("Nome","count"),
            kwp=("Potência estimada (kWp)","sum"),
            score=("Aurum Score","mean")
        ).sort_values("kwp", ascending=False)
        st.dataframe(by_cat, use_container_width=True)

        st.markdown("**Top 10 por Score**")
        st.dataframe(
            df[["Nome","Categoria","Aurum Score","Potência estimada (kWp)","Geração anual (kWh)","Endereço"]].head(10),
            use_container_width=True
        )

# ---------- Mapeamento atual ----------
with tab_map:
    st.subheader("🗺️ Mapa de Leads")
    df = st.session_state.df
    params = st.session_state.last_params or {}

    if df is not None and not df.empty:
        center_coords = geocode_location(params.get("local","Niterói"))
        m = folium.Map(location=[center_coords["lat"], center_coords["lon"]],
                       zoom_start=11, control_scale=True, tiles="OpenStreetMap")

        folium.Marker([params.get("base_lat", center_coords["lat"]),
                       params.get("base_lon", center_coords["lon"])],
                      popup="Base Operacional", icon=folium.Icon(color="red", icon="home")).add_to(m)

        for _, row in df.iterrows():
            phone_html = f"<a href='tel:{row['Telefone']}'>{row['Telefone']}</a>" if pd.notna(row["Telefone"]) else "—"
            site_html = f"<a href='{row['Site']}' target='_blank'>site</a>" if pd.notna(row["Site"]) else "—"
            maps_html = f"<a href='{row['Maps URL']}' target='_blank'>Google Maps</a>" if pd.notna(row["Maps URL"]) else "—"
            popup = folium.Popup(f"""
                <b>{row['Nome']}</b><br>
                {row['Endereço'] or '—'}<br>
                Tel: {phone_html} · {site_html} · {maps_html}<br>
                Cat: {row['Categoria']} · Score: {row['Aurum Score']}<br>
                Área: {row['Área telhado (m²)']} m² · kWp: {row['Potência estimada (kWp)']}
            """, max_width=380)
            folium.CircleMarker([row["Latitude"], row["Longitude"]],
                                radius=6, color="#FF8C00", fill=True, fill_color="#FF8C00",
                                popup=popup).add_to(m)
        st_folium(m, width=1200, height=600)

        st.subheader("📋 Tabela (resultado da busca)")
        st.dataframe(df, use_container_width=True)

        # Salvar no banco
        st.markdown("### 💾 Salvar este resultado no banco de leads")
        col1, col2, col3, col4 = st.columns([1,1,1,2])
        with col1:
            campanha = st.text_input("Campanha", value=params.get("local","Aurum RJ"))
        with col2:
            responsavel = st.selectbox("Responsável", ["Matheus","Hans","Vinicius","Aguiar","Carol"])
        with col3:
            estagio = st.selectbox("Estágio", ["Novo","Qualificado","Proposta","Negociação","Fechado-Ganho","Fechado-Perdido"], index=0)
        with col4:
            obs = st.text_input("Observação (opcional)", value="")

        if st.button(f"📥 Salvar {len(df)} leads no banco", type="primary"):
            df_to_save = df.copy()
            ts = pd.Timestamp.now(tz="America/Sao_Paulo")
            df_to_save["Campanha"] = campanha
            df_to_save["Responsável"] = responsavel
            df_to_save["Estágio"] = estagio
            df_to_save["Obs"] = obs
            df_to_save["Salvo_em"] = ts.strftime("%Y-%m-%d %H:%M:%S")
            df_to_save["Usuário"] = st.session_state.auth_user

            if st.session_state.saved_leads is None or st.session_state.saved_leads.empty:
                merged = df_to_save
            else:
                merged = pd.concat([st.session_state.saved_leads, df_to_save], ignore_index=True)

            merged.drop_duplicates(subset=["Nome","Latitude","Longitude"], keep="first", inplace=True)
            st.session_state.saved_leads = merged
            st.success(f"Salvo! Banco agora tem {len(st.session_state.saved_leads)} leads únicos.")
            try:
                save_leads_to_neon(df_to_save, st.session_state.auth_user)
                st.success("Leads enviados para o banco Neon.")
            except Exception as e:
                st.warning(f"Falha ao salvar no Neon: {e}")

        c1, c2 = st.columns(2)
        with c1:
            st.download_button("⬇️ Exportar resultado atual (CSV)",
                               data=df.to_csv(index=False).encode("utf-8"),
                               file_name="aurum_leads_resultado.csv", mime="text/csv")
        with c2:
            geojson = {
                "type": "FeatureCollection",
                "features": [
                    {"type": "Feature",
                     "geometry": {"type": "Point", "coordinates": [row["Longitude"], row["Latitude"]]},
                     "properties": {k: (v if not isinstance(v, (float, int)) else float(v))
                                    for k, v in row.items() if k not in ["Latitude","Longitude"]}}
                    for _, row in df.iterrows()
                ]
            }
            st.download_button("Exportar GeoJSON",
                               data=json.dumps(geojson, ensure_ascii=False).encode("utf-8"),
                               file_name="aurum_leads.geojson",
                               mime="application/geo+json")
    else:
        st.info("Execute um mapeamento na barra lateral.")

# ---------- Heatmap por Bairro ----------
with tab_heatmap:
    st.subheader("🔥 Heatmap por Bairro")
    df = st.session_state.saved_leads

    if df is None or df.empty:
        st.info("Sem leads salvos para gerar o heatmap por bairro.")
    else:
        categories = ["Todos"] + sorted(df["Categoria"].dropna().unique().tolist())
        with st.form("heatmap_form"):
            hm_category = st.selectbox("Tipo de negócio/edificação", categories)
            hm_limit = st.slider("Máx. pontos para geocodificar (Nominatim)", 50, 1000, 250, 50)
            hm_submit = st.form_submit_button("Gerar heatmap")

        if hm_submit:
            df_filtered = df if hm_category == "Todos" else df[df["Categoria"] == hm_category]
            if df_filtered.empty:
                st.warning("Sem dados para esse filtro.")
                st.session_state.heatmap_df = None
            else:
                if len(df_filtered) > hm_limit:
                    df_sample = df_filtered.sample(n=hm_limit, random_state=42)
                else:
                    df_sample = df_filtered.copy()
                st.info("Calculando bairros via Nominatim (pode levar alguns segundos)…")
                df_sample["Bairro"] = df_sample.apply(
                    lambda r: reverse_geocode_bairro(r["Latitude"], r["Longitude"]),
                    axis=1
                )
                st.session_state.heatmap_df = df_sample

        hm_df = st.session_state.heatmap_df
        if hm_df is None or hm_df.empty:
            st.info("Clique em **Gerar heatmap** para montar o mapa por bairro.")
        else:
            grouped = hm_df.groupby("Bairro", dropna=False).agg(
                leads=("Nome", "count"),
                lat=("Latitude", "mean"),
                lon=("Longitude", "mean")
            ).reset_index().sort_values("leads", ascending=False)

            st.markdown("### 📊 Concentração por bairro")
            st.dataframe(grouped, use_container_width=True)

            center_lat = hm_df["Latitude"].mean()
            center_lon = hm_df["Longitude"].mean()
            m_heat = folium.Map(location=[center_lat, center_lon], zoom_start=12, control_scale=True, tiles="OpenStreetMap")
            heat_data = [[row["lat"], row["lon"], row["leads"]] for _, row in grouped.iterrows()]
            HeatMap(heat_data, radius=25, blur=18, max_zoom=14).add_to(m_heat)
            st_folium(m_heat, width=1200, height=600)

# ---------- Leads salvos ----------
with tab_saved:
    st.subheader("📦 Banco de Leads (consolidado)")
    saved = st.session_state.saved_leads
    if saved is None or saved.empty:
        st.info("Ainda não há leads salvos. Salve na aba 'Mapeamento atual'.")
    else:
        f1, f2, f3 = st.columns(3)
        with f1:
            filtro_campanha = st.multiselect("Campanha", sorted(saved["Campanha"].dropna().unique().tolist()))
        with f2:
            filtro_resp = st.multiselect("Responsável", sorted(saved["Responsável"].dropna().unique().tolist()))
        with f3:
            filtro_estagio = st.multiselect("Estágio", sorted(saved["Estágio"].dropna().unique().tolist()))

        df_view = saved.copy()
        if filtro_campanha: df_view = df_view[df_view["Campanha"].isin(filtro_campanha)]
        if filtro_resp: df_view = df_view[df_view["Responsável"].isin(filtro_resp)]
        if filtro_estagio: df_view = df_view[df_view["Estágio"].isin(filtro_estagio)]

        st.caption(f"Mostrando {len(df_view)} de {len(saved)} leads.")
        st.dataframe(df_view, use_container_width=True)

        c1, c2, c3 = st.columns(3)
        with c1:
            st.download_button("⬇️ Exportar banco (CSV)",
                               data=df_view.to_csv(index=False).encode("utf-8"),
                               file_name="aurum_leads_banco.csv", mime="text/csv")
        with c2:
            up = st.file_uploader("📤 Importar/mesclar CSV", type=["csv"])
            if up is not None:
                try:
                    ext = pd.read_csv(up)
                    for col in ["Campanha","Responsável","Estágio","Obs","Salvo_em"]:
                        if col not in ext.columns: ext[col] = ""
                    for col in ["Nome","Latitude","Longitude"]:
                        if col not in ext.columns:
                            st.error(f"CSV precisa ter a coluna '{col}'."); ext = None; break
                    if ext is not None:
                        merged = pd.concat([st.session_state.saved_leads, ext], ignore_index=True)
                        merged.drop_duplicates(subset=["Nome","Latitude","Longitude"], keep="first", inplace=True)
                        st.session_state.saved_leads = merged
                        st.success(f"Misturado! Banco total: {len(merged)} leads únicos.")
                except Exception as e:
                    st.error(f"Falha ao importar CSV: {e}")
        with c3:
            if st.button("🧨 Limpar banco de leads"):
                st.session_state.saved_leads = None
                st.warning("Banco de leads apagado.")

# ---------- NOVA ABA: Maiores Telhados (com persistência) ----------
with tab_bigroofs:
    st.subheader("🏢 Maiores Telhados por Região (independente do tipo)")

    with st.form("form_big_roofs", clear_on_submit=False):
        # valores default vêm do estado, se existir
        br_default_center = st.session_state.big_roofs_center or {}
        br_default_params = st.session_state.big_roofs_params or {}

        st.markdown("**Região alvo (texto livre ou 'lat,lon')**")
        br_location = st.text_input("Local", value=br_default_center.get("name","Niterói"), key="br_location")
        br_radius_km = st.slider("Raio (km)", 2, 50, br_default_params.get("radius_km", 15), 1, key="br_radius_km")
        br_min_area = st.number_input("Área mínima do telhado (m²)", min_value=100.0, max_value=100000.0,
                                      value=br_default_params.get("min_area", 800.0), step=50.0, key="br_min_area")
        br_topn = st.slider("Top N", 10, 500, br_default_params.get("topn", 100), 10, key="br_topn")
        persist_toggle = st.checkbox("🔒 Manter resultado ao mudar controles", value=True, key="br_persist")
        br_submit = st.form_submit_button("🔎 Buscar maiores telhados")

    def rank_roofs(lat: float, lon: float, radius_m: int, min_area_m2: float = 600.0, top_n: int = 100) -> pd.DataFrame:
        buildings = overpass_buildings_geom_region(lat, lon, radius_m=radius_m)
        rows = []
        for poly in buildings:
            a = project_area_m2(poly)
            if a >= min_area_m2:
                c = poly.centroid
                rows.append({"Área telhado (m²)": round(a, 1),
                             "Latitude": float(c.y), "Longitude": float(c.x)})
        if not rows:
            return pd.DataFrame(columns=["Área telhado (m²)","Latitude","Longitude"])
        df = pd.DataFrame(rows).sort_values("Área telhado (m²)", ascending=False)
        return df.head(top_n)

    # SUBMIT → calcula e persiste
    if br_submit:
        st.info("Coletando footprints de prédios no OSM e calculando áreas…")
        # usa a chave do ambiente (se existir); se não, Nominatim cobre
        center = geocode_location(br_location, GOOGLE_PLACES_API_KEY)
        br_lat, br_lon = center["lat"], center["lon"]
        br_radius_m = int(br_radius_km * 1000)

        df_roofs = rank_roofs(br_lat, br_lon, br_radius_m, min_area_m2=br_min_area, top_n=br_topn)

        st.session_state.big_roofs_df = df_roofs
        st.session_state.big_roofs_center = {"lat": br_lat, "lon": br_lon, "name": br_location}
        st.session_state.big_roofs_params = {"radius_km": br_radius_km, "min_area": br_min_area, "topn": br_topn}

    # RENDER → usa o estado caso não haja novo submit
    df_roofs = st.session_state.big_roofs_df
    center = st.session_state.big_roofs_center

    if df_roofs is None or center is None or df_roofs.empty:
        st.info("Defina parâmetros e clique em **Buscar maiores telhados**.")
    else:
        br_lat, br_lon = center["lat"], center["lon"]
        st.markdown("### 🗺️ Mapa dos maiores telhados")
        m2 = folium.Map(location=[br_lat, br_lon], zoom_start=12, control_scale=True, tiles="OpenStreetMap")
        folium.Marker([br_lat, br_lon], popup=f"Centro: {center.get('name','—')}", icon=folium.Icon(color="red", icon="home")).add_to(m2)
        for _, row in df_roofs.iterrows():
            popup = folium.Popup(f"Área: {row['Área telhado (m²)']} m²", max_width=250)
            folium.CircleMarker([row["Latitude"], row["Longitude"]],
                                radius=6, color="#00d084", fill=True, fill_color="#00d084",
                                popup=popup).add_to(m2)
        st_folium(m2, width=1200, height=600)

        st.markdown("### 📋 Ranking (maiores primeiro)")
        st.dataframe(df_roofs, use_container_width=True)

        st.markdown("### ⬇️ Exportar")
        c1, c2 = st.columns(2)
        with c1:
            st.download_button("CSV", data=df_roofs.to_csv(index=False).encode("utf-8"),
                               file_name="maiores_telhados.csv", mime="text/csv")
        with c2:
            geojson = {
                "type": "FeatureCollection",
                "features": [
                    {"type":"Feature",
                     "geometry":{"type":"Point","coordinates":[row["Longitude"], row["Latitude"]]},
                     "properties":{"area_m2": float(row["Área telhado (m²)"])}}
                    for _, row in df_roofs.iterrows()
                ]
            }
            st.download_button("GeoJSON",
                               data=json.dumps(geojson, ensure_ascii=False).encode("utf-8"),
                               file_name="maiores_telhados.geojson",
                               mime="application/geo+json")

        # Se o usuário quiser comportamento volátil, limpamos quando trocar controles (sem novo submit)
        if not persist_toggle and not br_submit:
            st.session_state.big_roofs_df = None
            st.session_state.big_roofs_center = None
            st.session_state.big_roofs_params = None
