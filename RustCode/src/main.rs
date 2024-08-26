// I do not consider myself in any way a Rust programmer (yet)!
// GitHub Copilot gets most of the credit.

use std::collections::{HashMap, HashSet};
use indicatif::ProgressBar;
use indicatif::ProgressStyle;
use rand::{rngs::ThreadRng, Rng};

fn unit_propagation(mut cnf: Vec<Vec<i32>>, mut assignment: std::collections::HashMap<i32, bool>) -> (Vec<Vec<i32>>, std::collections::HashMap<i32, bool>) {
    let mut changed = true;
    while changed {
        changed = false;
        for clause in &cnf {
            let unassigned: Vec<i32> = clause.iter().cloned().filter(|&lit| !assignment.contains_key(&lit.abs()) && !assignment.contains_key(&-lit.abs())).collect();
            if unassigned.len() == 1 {
                let lit = unassigned[0];
                assignment.insert(lit.abs(), lit > 0);
                changed = true;
                cnf = simplify(cnf, lit);
                if cnf.is_empty() {
                    return (cnf, assignment);
                }
                break;
            }
        }
    }
    (cnf, assignment)
}

fn simplify(cnf: Vec<Vec<i32>>, lit: i32) -> Vec<Vec<i32>> {
    let mut new_cnf: Vec<Vec<i32>> = cnf.into_iter().filter(|clause| !clause.contains(&lit)).collect();
    for clause in &mut new_cnf {
        clause.retain(|&x| x != -lit);
    }
    new_cnf
}

fn pure_literal_elimination(mut cnf: Vec<Vec<i32>>, mut assignment: HashMap<i32, bool>) -> (Vec<Vec<i32>>, HashMap<i32, bool>) {
    let all_literals: HashSet<i32> = cnf.iter().flat_map(|clause| clause.iter().cloned()).collect();
    
    for &literal in &all_literals {
        if !all_literals.contains(&-literal) {
            assignment.insert(literal.abs(), literal > 0);
            cnf = simplify(cnf, literal);
        }
    }
    
    (cnf, assignment)
}

fn dpll(cnf: Vec<Vec<i32>>, input_assignment: Option<HashMap<i32, bool>>) -> (bool, HashMap<i32, bool>) {
    let assignment = input_assignment.unwrap_or_else(HashMap::new);

    let (cnf, assignment) = unit_propagation(cnf, assignment);

    let (cnf, mut assignment) = pure_literal_elimination(cnf, assignment);

    if cnf.is_empty() {
        return (true, assignment);
    }

    if cnf.iter().any(|clause| clause.is_empty()) {
        return (false, HashMap::new());
    }

    // Choose a variable (decision step)
    let unassigned_vars: HashSet<i32> = cnf.iter()
        .flat_map(|clause| clause.iter())
        .filter(|&&literal| !assignment.contains_key(&literal.abs()))
        .map(|&literal| literal.abs())
        .collect();

    if let Some(&chosen_var) = unassigned_vars.iter().next() {
        assignment.insert(chosen_var, true);
        let simplified_cnf = simplify(cnf.clone(), chosen_var);
        let (result, final_assignment) = dpll(simplified_cnf, Some(assignment.clone()));
        if result {
            return (true, final_assignment);
        }

        assignment.insert(chosen_var, false);
        let simplified_cnf = simplify(cnf, -chosen_var);
        return dpll(simplified_cnf, Some(assignment));
    }

    (false, HashMap::new()) 
}

fn is_clause_satisfied(clause: &Vec<i32>, assignment: &HashMap<i32, bool>) -> bool {
    clause.iter().any(|&lit| {
        let var = lit.abs();
        let is_positive = lit > 0;
        assignment.get(&var) == Some(&is_positive)
    })
}

fn count_unsatisfied_clauses(cnf: &Vec<Vec<i32>>, assignment: &HashMap<i32, bool>) -> usize {
    cnf.iter().filter(|clause| !is_clause_satisfied(clause, assignment)).count()
}

fn count_unsat_clauses_if_flipped(var: i32, cnf: &Vec<Vec<i32>>, assignment: &HashMap<i32, bool>) -> usize {
    let mut new_assignment = assignment.clone();
    new_assignment.insert(var, !new_assignment.get(&var).unwrap_or(&false));
    count_unsatisfied_clauses(cnf, &new_assignment)
}

fn get_vars(cnf: &Vec<Vec<i32>>) -> HashSet<i32> {
    cnf.iter().flat_map(|clause| clause.iter().cloned().map(|lit| lit.abs())).collect()
}

fn walk_sat(cnf: Vec<Vec<i32>>, rng: &mut ThreadRng, mut assignment: HashMap<i32, bool>, max_flips: usize, p: f64) -> (bool, HashMap<i32, bool>) {
    let cnf = cnf;
    let mut unsat_clauses = count_unsatisfied_clauses(&cnf, &assignment);
    for _ in 0..max_flips {
        if unsat_clauses == 0 {
            return (true, assignment);
        }
        let flip = rng.gen_bool(p);
        if flip {
            // Randomly choose a variable to flip
            let vars = get_vars(&cnf);
            let var = *vars.iter().nth(rng.gen_range(0..vars.len())).unwrap();
            assignment.insert(var, !assignment.get(&var).unwrap_or(&false));
            unsat_clauses = count_unsat_clauses_if_flipped(var, &cnf, &assignment);
        } else {
            // Choose the variable that maximizes the number of satisfied clauses
            let mut best_var = None;
            let mut best_score = unsat_clauses;
            for &var in assignment.keys() {
                let score = count_unsat_clauses_if_flipped(var, &cnf, &assignment);
                if score < best_score {
                    best_score = score;
                    best_var = Some(var);
                }
            }
            if let Some(best_var) = best_var {
                assignment.insert(best_var, !assignment.get(&best_var).unwrap_or(&false));
                unsat_clauses = best_score;
            }
        }
    }
    (false, HashMap::new())
}

fn random_cnf(num_vars: usize, num_clauses: usize) -> Vec<Vec<i32>> {
    let mut rng = rand::thread_rng();
    let mut cnf = Vec::new();
    for _ in 0..num_clauses {
        let clause_len = rng.gen_range(1..=3);
        let clause: Vec<i32> = (0..clause_len).map(|_| {
            let var = rng.gen_range(1..=num_vars);
            let sign = if rng.gen_bool(0.5) { 1 } else { -1 };
            sign * var as i32
        }).collect();
        cnf.push(clause);
    }
    cnf
}

fn proccess_combination(num_vars: usize, num_clauses: usize, algorithm: &str, rng: &mut ThreadRng) -> Vec<String> {
    let cnf = random_cnf(num_vars, num_clauses);
    let start = std::time::Instant::now();
    let (_, _) = if algorithm == "dpll" {
        dpll(cnf, None)
    } else {
        walk_sat(cnf, rng, HashMap::new(), 100, 0.5)
    };
    let time = start.elapsed().as_secs_f64();
    vec![num_vars.to_string(), num_clauses.to_string(), time.to_string(), algorithm.to_string()]
}

fn save_csv(data: Vec<Vec<String>>, filename: &str) {
    let mut wtr = csv::Writer::from_path(filename).unwrap();
    wtr.write_record(&["num_symbols", "num_clauses", "time", "algorithm"]).unwrap();
    for row in data {
        wtr.write_record(row).unwrap();
    }
    wtr.flush().unwrap();
}

fn main() {
    let mut rng = rand::thread_rng();
    let mut results: Vec<Vec<String>> = Vec::new();
    let symbol_start = 2 as usize;
    let symbol_end = 50 as usize;
    let clause_start = 2 as usize;
    let clause_end = 50 as usize;
    let rep_count = 1000 as u64;
    let rep_count_size = rep_count as usize;
    let pb = ProgressBar::new(((symbol_end - symbol_start) * (clause_end - clause_start) * rep_count_size) as u64);
    pb.set_style(ProgressStyle::default_bar()
        .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta})").unwrap()
    );
    
    for num_symbols in symbol_start..=symbol_end {
        for num_clauses in clause_start..=clause_end {
            for _ in 0..rep_count {
                results.push(proccess_combination(num_symbols, num_clauses, "dpll", &mut rng));
                results.push(proccess_combination(num_symbols, num_clauses, "walksat", &mut rng));
            }
            pb.inc(rep_count);
        }
    }
    save_csv(results, "results-more.csv");
}