import math

from shapely.geometry import Polygon

from src.geom_metrics import compute_metrics


def test_rectangle_metrics():
    rect = Polygon([(0, 0), (20, 0), (20, 10), (0, 10)])
    metrics = compute_metrics(rect)
    assert metrics.area_m2 == 200
    assert math.isclose(metrics.rectangularity, 1.0, abs_tol=1e-6)
    assert metrics.aspect_ratio == 2.0
    assert metrics.hole_area_ratio == 0.0


def test_l_shape_metrics():
    l_shape = Polygon([(0, 0), (10, 0), (10, 4), (4, 4), (4, 10), (0, 10)])
    metrics = compute_metrics(l_shape)
    assert metrics.rectangularity < 1.0
    assert metrics.convexity < 1.0


def test_polygon_with_hole():
    outer = [(0, 0), (10, 0), (10, 10), (0, 10)]
    inner = [(3, 3), (7, 3), (7, 7), (3, 7)]
    polygon = Polygon(outer, [inner])
    metrics = compute_metrics(polygon)
    assert math.isclose(metrics.hole_area_ratio, 0.19, abs_tol=0.01)
