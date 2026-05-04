// Minimal fixture for Styx golden tests.
// Covers: enums, structs, loops, match, Result, Vec operations.

/// Simple 3-variant enum.
pub enum Color {
    Red,
    Green,
    Blue,
}

/// Struct with scalar fields.
pub struct Point {
    pub x: u64,
    pub y: u64,
}

/// Struct with Vec field.
pub struct Polygon {
    pub vertices: Vec<Point>,
    pub color: Color,
}

/// Function with a while loop: sum values 0..n.
pub fn sum_up_to(n: u64) -> u64 {
    let mut i: u64 = 0;
    let mut acc: u64 = 0;
    while i < n {
        acc += i;
        i += 1;
    }
    acc
}

/// Function with match expression.
pub fn color_code(c: &Color) -> u64 {
    match c {
        Color::Red => 0,
        Color::Green => 1,
        Color::Blue => 2,
    }
}

/// Linear search in a Vec.
pub fn find_index(points: &Vec<Point>, target_x: u64) -> Option<usize> {
    let len = points.len();
    let mut i: usize = 0;
    while i < len {
        if points[i].x == target_x {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Function returning Result with early return.
pub fn checked_distance(a: &Point, b: &Point) -> Result<u64, &'static str> {
    if a.x > b.x {
        return Err("a.x > b.x");
    }
    if a.y > b.y {
        return Err("a.y > b.y");
    }
    let dx = b.x - a.x;
    let dy = b.y - a.y;
    Ok(dx + dy)
}

/// Polygon perimeter (loop over Vec with index).
pub fn polygon_vertex_count(p: &Polygon) -> usize {
    p.vertices.len()
}
