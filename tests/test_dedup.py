from shapely.geometry import Polygon

from src.filters import deduplicate, iou


def test_iou_dedup():
    poly_a = Polygon([(0, 0), (10, 0), (10, 10), (0, 10)])
    poly_b = Polygon([(1, 1), (9, 1), (9, 9), (1, 9)])
    assert iou(poly_a, poly_b) > 0.6
    candidates = [
        {"geometry": poly_a, "pre_score": 10},
        {"geometry": poly_b, "pre_score": 20},
    ]
    kept, removed = deduplicate(candidates, iou_threshold=0.6)
    assert len(kept) == 1
    assert removed == 1
    assert kept[0]["pre_score"] == 20
