use std::collections::HashSet;

pub mod dataset;


// Adjacency list
pub type Graph = Vec<Vec<usize>>;

// Given a graph and a sequence rev_peo, checks if rev_peo is a reversed PEO.
// O(V + E)-time
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
/// Complexity: O(V + E)
pub fn get_perfect_elimination_ordering(g: &Graph) -> Option<Vec<usize>> {
    let n = g.len();
    let mut peo = Vec::new();
    // State
    struct State {
        border: Vec<usize>,
        arr: Vec<(usize, usize)>,
        comm: Vec<usize>,
        processed: Vec<bool>,
        inv: Vec<usize>,
        remaining: usize,
    }
    impl State {
        fn increment(&mut self, idx: usize) {
            let pos = self.inv[idx];
            let staging = self.border[self.comm[idx] + 1] - 1;
            let staging_idx = self.arr[staging].0;
            self.arr.swap(pos, staging);
            self.inv.swap(idx, staging_idx);
            self.arr[staging].1 += 1;
            self.border[self.comm[idx] + 1] -= 1;
            self.comm[idx] += 1;
            if self.border[self.comm[idx]] == self.remaining - 1 {
                let max = self.comm[idx];
                self.border[max + 1] = self.remaining;
            }
        }
        fn pop_max(&mut self) -> usize {
            let index = self.remaining - 1;
            let max = self.arr[index].1;
            let comm_index = self.arr[index].0;
            self.border[max + 1] -= 1;
            if self.remaining > 0 { self.remaining -= 1; }
            self.processed[comm_index] = true;
            comm_index
        }
    }
    let mut state = State {
        border: vec![0; n + 1],
        arr: vec![(0, 0); n],
        comm: vec![0; n], // |N(v) /\ Y|
        processed: vec![false; n],
        inv: vec![0; n],
        remaining: n,
    };
    for i in 0 .. n { state.arr[i] = (i, 0); }
    state.border[1] = n;
    for i in 0 .. n { state.inv[i] = i; }
    for _ in 0 .. n {
        let index = state.pop_max();
        peo.push(index);
        for &w in g[index].iter() {
            if !state.processed[w] {
                state.increment(w);
            }
        }
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
    use ::dataset;
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
    // This example is taken from http://chocobaby-aporo.hatenablog.com/entry/2017/11/12/094759.
    #[test]
    fn sample_not_chordal_1() {
        let g = make_graph(9, &[(0, 1), (0, 2), (0, 3), (0, 5), (1, 2),
                                (1, 4), (1, 5), (1, 6), (2, 3), (3, 4),
                                (3, 6), (3, 8), (4, 8), (5, 6), (6, 7),
                                (7, 8)]);
        assert_eq!(get_perfect_elimination_ordering(&g), None);
    }
    #[test]
    fn sample_chordal_but_not_interval() {
        let g = make_graph(6, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
                                (5, 0), (0, 2), (2, 4), (4, 0)]);
        assert!(is_chordal(&g));
        let peo = get_perfect_elimination_ordering(&g).unwrap();
        assert!(naive_is_peo(&g, &peo));
    }
    #[test]
    fn test_check_peo() {
        let g = make_graph(4, &[(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)]);
        let mut not_peo = vec![0, 1, 2, 3];
        assert!(!naive_is_peo(&g, &not_peo));
        not_peo.reverse();
        assert!(!check_peo(&g, &not_peo));
        let mut peo = vec![1, 0, 2, 3];
        assert!(naive_is_peo(&g, &peo));
        peo.reverse();
        assert!(check_peo(&g, &peo));
    }
    // Reads graphs from a dataset in graph6 format.
    // Datasets are from https://users.cecs.anu.edu.au/~bdm/data/graphs.html.
    fn test_dataset(filename: &str) {
        let graphs = dataset::read_from_file(filename).unwrap();
        for graph in graphs {
            assert!(is_chordal(&graph));
            let peo = get_perfect_elimination_ordering(&graph).unwrap();
            assert!(naive_is_peo(&graph, &peo));
        }
    }
    #[test]
    fn test_dataset4() {
        test_dataset("dataset/chordal4.g6");
    }
    #[test]
    fn test_dataset5() {
        test_dataset("dataset/chordal5.g6");
    }
    #[test]
    fn test_dataset6() {
        test_dataset("dataset/chordal6.g6");
    }
    #[test]
    fn test_dataset7() {
        test_dataset("dataset/chordal7.g6");
    }
}
