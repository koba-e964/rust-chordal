use Graph;
use std::io::{BufRead, BufReader, Result};
use std::fs::File;

// https://users.cecs.anu.edu.au/~bdm/data/graphs.html
pub fn read_from_file(filename: &str) -> Result<Vec<Graph>> {
    let fd = File::open(filename)?;
    let buf_reader = BufReader::new(fd);
    let mut graphs = Vec::new();
    for line in buf_reader.lines() {
        let line = line?;
        let graph = parse_graph6(line);
        graphs.push(graph);
    }
    Ok(graphs)
}

/// Parses a graph encoded in graph6 format.
/// Reference: https://users.cecs.anu.edu.au/~bdm/data/formats.txt
pub fn parse_graph6(dat: String) -> Graph {
    let vec = graph6_to_6bitvector(dat);
    let n;
    let header_len;
    if vec[0] != 63 {
        n = vec[0] as usize;
        header_len = 1;
    } else if vec[1] != 63 {
        n = ((vec[1] as usize) << 12) + ((vec[2] as usize) << 6)
            + (vec[3] as usize);
        header_len = 4;
    } else {
        let mut v = 0;
        for i in 0 .. 6 {
            v <<= 6;
            v += vec[i + 2] as usize;
        }
        n = v;
        header_len = 8;
    }
    let mut graph = vec![Vec::new(); n];
    let mut pos = 6 * header_len;
    for i in 1 .. n {
        for j in 0 .. i {
            let bit = (vec[pos / 6] >> (5 - pos % 6) & 1) != 0;
            if bit {
                graph[i].push(j);
                graph[j].push(i);
            }
            pos += 1;
        }
    }
    graph
}


fn graph6_to_6bitvector(dat: String) -> Vec<u8> {
    dat.chars().map(|c| c as u8 - 63u8).collect()
}
