use std::collections::{BinaryHeap, HashSet};

// Adjacency list
pub type Graph = Vec<Vec<usize>>;

// Given a graph and reversed peo, checks if peo is a reversed PEO.
fn check_peo(g: &Graph, rev_peo: &[usize]) -> bool {
    let n = g.len();
    let mut inv_rev_peo = vec![0; n];
    for i in 0 .. n {
        inv_rev_peo[rev_peo[i]] = i;
    }
    let mut permuted_g = vec![Vec::new(); n];
    for i in 0 .. n {
        for &w in g[i].iter() {
            permuted_g[inv_rev_peo[i]].push(inv_rev_peo[w]);
        }
    }
    let mut neighbor = vec![HashSet::new(); n];
    let mut max_neighbor = vec![0; n]; // bias: +1
    for i in 0 .. n {
        for &w in permuted_g[i].iter() {
            if w < i {
                neighbor[i].insert(w);
                max_neighbor[i] = std::cmp::max(max_neighbor[i], w + 1);
            }
        }
    }
    for i in 0 .. n {
        if max_neighbor[i] > 0 {
            let max = max_neighbor[i] - 1;
            // neighbor[max] \supseteq neighbor[i] - {max} ?
            let diff: Vec<usize> = neighbor[i].difference(&neighbor[max])
                .cloned().collect();
            if diff != vec![max] {
                return false;
            }
        }
    }
    true
}

pub fn is_chordal(g: &Graph) -> bool {
    get_perfect_elimination_ordering(g).is_some()
}

/// Maximum cardinality search
/// Reference: http://chocobaby-aporo.hatenablog.com/entry/2017/11/12/094759
/// (written in Japanese)
/// Complexity: O(E log V)
pub fn get_perfect_elimination_ordering(g: &Graph) -> Option<Vec<usize>> {
    let n = g.len();
    let mut que = BinaryHeap::new();
    let mut comm = vec![0; n]; // |N(v) /\ Y|
    let mut remaining = n;
    let mut processed = vec![false; n];
    let mut peo = Vec::new();
    for i in 0 .. n {
        que.push((0, i));
    }
    while let Some((_common_cardinality, index)) = que.pop() {
        if remaining == 0 { break; }
        if processed[index] { continue; }
        processed[index] = true;
        peo.push(index);
        for &w in g[index].iter() {
            if !processed[w] {
                comm[w] += 1;
                que.push((comm[w], w));
            }
        }
        remaining -= 1;
    }
    if check_peo(g, &peo) {
        peo.reverse();
        Some(peo)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    fn make_graph(n: usize, edges: &[(usize, usize)]) -> Graph {
        let mut g = vec![Vec::new(); n];
        for &(u, v) in edges {
            g[u].push(v);
            g[v].push(u);
        }
        g
    }
    // This takes O(V * E).
    fn naive_is_peo(g: &Graph, peo: &[usize]) -> bool {
        let n = g.len();
        let mut g_set = vec![HashSet::new(); n];
        for i in 0 .. n {
            for &w in g[i].iter() {
                g_set[i].insert(w);
            }
            g_set[i].insert(i); // for simplicity, ensures i in g_set[i].
        }
        // Iteratively checks peo[i], and eliminate peo[i] from g_set.
        for &v in peo.iter() {
            // Is N(v) clique?
            let nv = g_set[v].clone();
            for &u in nv.iter() {
                if !nv.is_subset(&g_set[u]) {
                    return false;
                }
            }
            // Delete v
            for w in nv {
                g_set[w].remove(&v);
            }
            g_set[v].clear();
        }
        true
    }
    #[test]
    fn cycle_with_4_vertices_is_not_chordal() {
        let g = make_graph(4, &[(0, 1), (1, 2), (2, 3), (3, 0)]);
        assert_eq!(get_perfect_elimination_ordering(&g), None);
    }
    #[test]
    fn cycle_with_5_vertices_is_not_chordal() {
        let g = make_graph(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
        assert_eq!(get_perfect_elimination_ordering(&g), None);
    }
    #[test]
    fn square_slash_is_chordal() {
        let g = make_graph(4, &[(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)]);
        assert!(is_chordal(&g));
        let peo = get_perfect_elimination_ordering(&g).unwrap();
        assert!(naive_is_peo(&g, &peo));
    }
    // This example is taken from http://chocobaby-aporo.hatenablog.com/entry/2017/11/04/180325.
    #[test]
    fn sample_chordal_1() {
        let g = make_graph(9, &[(0, 4), (0, 5), (0, 6), (1, 2), (1, 8),
                                (2, 6), (2, 7), (2, 8), (3, 4), (3, 5),
                                (3, 8), (4, 5), (4, 6), (4, 8), (5, 6),
                                (5, 7), (5, 8), (6, 7), (6, 8), (7, 8)]);
        assert!(is_chordal(&g));
        let peo = get_perfect_elimination_ordering(&g).unwrap();
        assert!(naive_is_peo(&g, &peo));
    }
}
