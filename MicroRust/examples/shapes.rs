// A small Rust program in the MicroRust subset: an enum, a trait, an impl, pattern matching.

use std::cmp::max;

pub enum Shape {
    Circle { radius: u32 },
    Rect { width: u32, height: u32 },
    Unit,
}

pub trait Area {
    fn area(&self) -> u32;
}

impl Area for Shape {
    fn area(&self) -> u32 {
        match self {
            Shape::Circle { radius } => 3 * radius * radius,
            Shape::Rect { width, height } => width * height,
            Shape::Unit => 1,
        }
    }
}

const LIMIT: u32 = 100;

fn total(shapes: &[Shape]) -> u32 {
    let mut sum = 0;
    for s in shapes {
        if s.area() > 0 {
            sum += s.area();
        }
    }
    max(sum, LIMIT)
}

fn biggest(a: u32, b: u32) -> u32 {
    if a >= b { a } else { b }
}
