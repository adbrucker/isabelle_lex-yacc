// uRust style: references, a while loop with a fuel attribute, early return, a swap.

fn swap(a: &mut u32, b: &mut u32) {
    let old_a = *a;
    let old_b = *b;
    *a = old_b;
    *b = old_a;
}

fn count_down(n: u32) -> u32 {
    let mut i = n;
    let mut steps = 0;
    #[fuel(100)]
    while i > 0 {
        i -= 1;
        steps += 1;
    }
    steps
}

fn find(xs: &[u32], target: u32) -> Option<usize> {
    let mut i = 0;
    while i < xs.len() {
        if xs[i] == target {
            return Some(i);
        }
        i += 1;
    }
    None
}
