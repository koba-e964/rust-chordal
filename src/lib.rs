use std::collections::{HashSet, HashMap};

pub mod dataset;


// Adjacency list
pub type Graph = Vec<Vec<usize>>;

fn get_induced_cycle(g: &Graph, init0: usize, init1: usize, init2: usize) -> Vec<usize> {
    let n = g.len();
    assert!(init1 > init0);
    assert!(init2 < init0);
    let mut chordless = vec![n; n]; // filled with out-of-range values
    chordless.append(&mut vec![init0, init1, init2]);
    chordless.append(&mut vec![n; n]);
    let mut chordless_inv: HashMap<usize, usize> = (0 .. chordless.len()).map(|i| (chordless[i], i)).collect();
    let mut lo = n;
    let mut hi = n + 3;
    let mut rev = false; // if chordless is interpreted as a reversed path
    loop {
        let v0 = chordless[lo];
        let vk = chordless[hi - 1];
        let (v0, vk) = if rev { (vk, v0) } else { (v0, vk) };
        assert!(v0 > vk);
        // v[k - 1]
        let vkm1 = if rev { chordless[lo + 1] } else { chordless[hi - 2] };
        assert!(v0 < vkm1);
        let mut next = None;
        let mut nvk = HashSet::new(); // N[v[k]]
        for &w in g[vk].iter() {
            nvk.insert(w);
        }
        let mut nvkm1 = HashSet::new(); // N[v[k - 1]]
        for &w in g[vkm1].iter() {
            nvkm1.insert(w);
        }
        for &w in g[v0].iter() {
            if w >= v0 { continue; }
            if nvk.contains(&w) && nvkm1.contains(&w) { continue; }
            next = Some(w);
            break;
        }
        let next = next.expect(&format!("g = {:?}", g));
        // Enumerate all chords from next.
        let ma_init = if rev { 3 * n } else { 0 };
        let mut ma_ind = ma_init;
        let mut vk_next = false; // Is (vk, next) in E?
        for &w in g[next].iter() {
            if chordless_inv.contains_key(&w) {
                let target = chordless_inv[&w];
                if rev {
                    if target != lo {
                        if target != hi - 1 {
                            ma_ind = ::std::cmp::min(ma_ind, target);
                        }
                    } else {
                        vk_next = true;
                    }
                } else {
                    if target != hi - 1 {
                        if target != lo {
                            ma_ind = ::std::cmp::max(ma_ind, target);
                        }
                    } else {
                        vk_next = true;
                    }
                }
            }
        }
        if ma_ind != ma_init {
            if rev {
                for i in ma_ind + 1 .. hi {
                    chordless_inv.remove(&chordless[i]);
                }
                hi = ma_ind + 2;
            } else {
                for i in lo .. ma_ind {
                    chordless_inv.remove(&chordless[i]);
                }
                lo = ma_ind - 1;
            }
        } else {
            if rev {
                hi += 1;
            } else {
                lo -= 1;
            }
        }
        if rev {
            chordless[hi - 1] = next;
            chordless_inv.insert(next, hi - 1);
        } else {
            chordless[lo] = next;
            chordless_inv.insert(next, lo);
        }
        rev = chordless[lo] < chordless[hi - 1];
        if vk_next { break; }
    }
    if rev { chordless[lo .. hi].reverse(); }
    chordless[lo .. hi].to_vec()
}

// Given a graph and a sequence rev_peo, checks if rev_peo is a reversed PEO.
// If rev_peo is a reversed PEO, this function returns Ok(()).
// Otherwise, it returns Err(induced_cycle_of_length_at_least_4).
// O(V + E)-time
fn check_peo(g: &Graph, rev_peo: &[usize]) -> Result<(), Vec<usize>> {
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
                .cloned().filter(|&v| v != max).collect();
            if !diff.is_empty() {
                // Find a chordless path of length 2
                let v = diff[0];
                let raw_induced = get_induced_cycle(&permuted_g, max, i, v);
                let mut induced = vec![0; raw_induced.len()];
                for j in 0 .. raw_induced.len() {
                    induced[j] = rev_peo[raw_induced[j]];
                }
                return Err(induced);
            }
        }
    }
    Ok(())
}

pub fn is_chordal(g: &Graph) -> bool {
    get_perfect_elimination_ordering(g).is_ok()
}

/// Maximum cardinality search
/// Reference: http://chocobaby-aporo.hatenablog.com/entry/2017/11/12/094759
/// (written in Japanese)
/// Complexity: O(V + E)
pub fn get_perfect_elimination_ordering(g: &Graph) -> Result<Vec<usize>, Vec<usize>> {
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
    check_peo(g, &peo)?;
    peo.reverse();
    Ok(peo)
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
    // Checks if cycle is an induced cycle of size >= 4.
    fn naive_is_induced_cycle_4(g: &Graph, cycle: &[usize]) -> bool {
        let n = g.len();
        if cycle.len() <= 3 { return false; }
        let mut induced = vec![Vec::new(); n];
        let mut cycle_v = HashSet::new();
        for &c in cycle.iter() {
            // Are all elements distinct?
            if cycle_v.contains(&c) { return false; }
            cycle_v.insert(c);
        }
        for i in 0 .. n {
            if !cycle.contains(&i) { continue; }
            for &w in g[i].iter() {
                if cycle.contains(&w) {
                    induced[i].push(w);
                }
            }
        }
        let m = cycle.len();
        for i in 0 .. m {
            let u = cycle[(i + m - 1) % m];
            let v = cycle[(i + 1) % m];
            if induced[cycle[i]] == [u, v] || induced[cycle[i]] == [v, u] {
                continue;
            } else {
                return false;
            }
        }
        true
    }
    fn assert_is_chordal(g: &Graph) {
        assert!(is_chordal(g));
        let peo = get_perfect_elimination_ordering(g).unwrap();
        assert!(naive_is_peo(g, &peo));
    }
    fn assert_is_not_chordal(g: &Graph) {
        assert!(!is_chordal(g));
        let induced_cycle = get_perfect_elimination_ordering(&g).err().unwrap();
        assert!(naive_is_induced_cycle_4(&g, &induced_cycle));
    }
    fn check_evidence_of_is_chordal(g: &Graph) {
        match get_perfect_elimination_ordering(&g) {
            Ok(peo) => assert!(naive_is_peo(g, &peo)),
            Err(induced_cycle) =>
                assert!(naive_is_induced_cycle_4(&g, &induced_cycle),
                "g = {:?}, cycle = {:?}", g, induced_cycle),
        }
    }
    #[test]
    fn cycle_with_4_vertices_is_not_chordal() {
        let g = make_graph(4, &[(0, 1), (1, 2), (2, 3), (3, 0)]);
        assert_is_not_chordal(&g);
    }
    #[test]
    fn cycle_with_5_vertices_is_not_chordal() {
        let g = make_graph(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
        assert_is_not_chordal(&g);
    }
    #[test]
    fn square_slash_is_chordal() {
        let g = make_graph(4, &[(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)]);
        assert_is_chordal(&g);
    }
    // This example is taken from http://chocobaby-aporo.hatenablog.com/entry/2017/11/04/180325.
    #[test]
    fn sample_chordal_1() {
        let g = make_graph(9, &[(0, 4), (0, 5), (0, 6), (1, 2), (1, 8),
                                (2, 6), (2, 7), (2, 8), (3, 4), (3, 5),
                                (3, 8), (4, 5), (4, 6), (4, 8), (5, 6),
                                (5, 7), (5, 8), (6, 7), (6, 8), (7, 8)]);
        assert_is_chordal(&g);
    }
    // This example is taken from http://chocobaby-aporo.hatenablog.com/entry/2017/11/12/094759.
    #[test]
    fn sample_not_chordal_1() {
        let g = make_graph(9, &[(0, 1), (0, 2), (0, 3), (0, 5), (1, 2),
                                (1, 4), (1, 5), (1, 6), (2, 3), (3, 4),
                                (3, 6), (3, 8), (4, 8), (5, 6), (6, 7),
                                (7, 8)]);
        assert_is_not_chordal(&g);
    }
    #[test]
    fn sample_chordal_but_not_interval() {
        let g = make_graph(6, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
                                (5, 0), (0, 2), (2, 4), (4, 0)]);
        assert_is_chordal(&g);
    }
    #[test]
    fn test_check_peo() {
        let g = make_graph(4, &[(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)]);
        let mut peo = vec![1, 0, 2, 3];
        assert!(naive_is_peo(&g, &peo));
        peo.reverse();
        assert!(check_peo(&g, &peo).is_ok());
    }
    #[test]
    fn test_check_not_chordal_challenge_1() {
        let g = make_graph(7, &[(0, 4), (0, 5), (1, 4), (1, 6), (2, 5),
                                (2, 6), (3, 5), (3, 6), (5, 6)]);
        assert_is_not_chordal(&g);
    }
    // Reads graphs from a dataset in graph6 format.
    // Datasets are from https://users.cecs.anu.edu.au/~bdm/data/graphs.html.
    fn test_dataset(filename: &str) {
        let graphs = dataset::read_from_file(filename).unwrap();
        for graph in graphs {
            assert_is_chordal(&graph);
        }
    }
    fn test_general_graph_dataset(filename: &str) {
        let graphs = dataset::read_from_file(filename).unwrap();
        for graph in graphs {
            check_evidence_of_is_chordal(&graph);
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
    #[test]
    fn test_graph4() {
        test_general_graph_dataset("dataset/graph4.g6");
    }
    #[test]
    fn test_graph5() {
        test_general_graph_dataset("dataset/graph5.g6");
    }
    #[test]
    fn test_graph6() {
        test_general_graph_dataset("dataset/graph6.g6");
    }
    #[test]
    fn test_graph7() {
        test_general_graph_dataset("dataset/graph7.g6");
    }
}
