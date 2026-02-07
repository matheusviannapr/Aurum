# Aurum Roof Lead Pipeline

Pipeline CLI para reescrever a identificação de telhados OSM e gerar leads FV de alta qualidade.

## Requisitos

- Python 3.11+
- Bibliotecas: requests/httpx, shapely, pyproj, geopandas, rtree (ou pygeos), pandas

## Instalação

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

## Uso

### Exemplo (Rio de Janeiro)

```bash
python -m src.main \
  --bbox "-43.403,-23.066,-43.110,-22.820" \
  --min_area_m2 300 \
  --target mixed \
  --tile_size_deg 0.01 \
  --out_dir outputs
```

### Saídas

- `candidates.geojson`: geometrias + propriedades + score
- `candidates.csv`: tabela sem geometrias
- `report.md`: estatísticas por etapa e top 50

## Notas

- O pipeline divide a AOI em tiles e consulta o Overpass em paralelo.
- Telhados com tags explícitas de solar são excluídos.
- A orientação para o norte é tratada como heurística (baixa confiança quando inferida).
