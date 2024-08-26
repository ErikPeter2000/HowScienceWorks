// I do not consider myself in any way a Rust programmer (yet)!
// GitHub Copilot gets most of the credit.

use indicatif::ProgressBar;
use indicatif::ProgressStyle;
use rand::{rngs::ThreadRng, Rng};
use std::collections::{HashMap, HashSet};

fn is_clause_satisfied(clause: &Vec<i32>, assignment: &HashMap<i32, bool>) -> bool {
    let result = clause.iter().any(|&lit| {
        let var = lit.abs();
        let result = *assignment.get(&var).unwrap_or(&false) == (lit > 0);
        result
    });
    result
}

fn is_cnf_satisfied(cnf: &Vec<Vec<i32>>, assignment: &HashMap<i32, bool>) -> bool {
    cnf.iter()
        .all(|clause| is_clause_satisfied(clause, assignment))
}

fn is_cnf_unsatisfied(cnf: &Vec<Vec<i32>>, assignment: &HashMap<i32, bool>) -> bool {
    return cnf.iter().any(|clause| {
        if clause
            .iter()
            .all(|&lit| assignment.contains_key(&lit.abs()))
        {
            is_clause_satisfied(clause, &assignment)
        } else {
            false
        }
    });
}

// Returns a symbol and the truth value of the pure symbol
fn find_pure_symbol(
    cnf: &Vec<Vec<i32>>,
    symbols: &HashSet<i32>,
    assignment: &HashMap<i32, bool>,
) -> (Option<i32>, Option<bool>) {
    let all_literals: HashSet<i32> = cnf
        .iter()
        .flat_map(|clause| clause.iter().cloned())
        .collect();

    for &symbol in symbols {
        if !assignment.contains_key(&symbol)
            && !all_literals.contains(&symbol)
            && !all_literals.contains(&-symbol)
        {
            return (
                Some(symbol),
                Some(assignment.get(&symbol).cloned().unwrap_or(false)),
            );
        }
    }

    (None, None)
}

fn find_unit_clause(
    cnf: &Vec<Vec<i32>>,
    assignment: &HashMap<i32, bool>,
) -> (Option<i32>, Option<bool>) {
    for clause in cnf {
        let unassigned: Vec<i32> = clause
            .iter()
            .cloned()
            .filter(|&lit| {
                !assignment.contains_key(&lit.abs()) && !assignment.contains_key(&-lit.abs())
            })
            .collect();
        if unassigned.len() == 1 {
            let lit = unassigned[0];
            return (Some(lit.abs()), Some(lit > 0));
        }
    }

    (None, None)
}

// function DPLL(clauses, symbols, model) returns true or false
//     if every clause in clauses is true in model then return true
//     if some clause in clauses is false in model then return false
//     P, value←FIND-PURE-SYMBOL(symbols, clauses, model)
//     if P is non-null then return DPLL(clauses, symbols – P, model ∪ {P=value})
//     P, value←FIND-UNIT-CLAUSE(clauses, model)
//     if P is non-null then return DPLL(clauses, symbols – P, model ∪ {P=value})
//     P←FIRST(symbols); rest ←REST(symbols)
//     return DPLL(clauses, rest, model ∪ {P=true}) or
//     DPLL(clauses, rest, model ∪ {P=false}))

fn dpll_with_assignment(
    cnf: Vec<Vec<i32>>,
    symbols: &HashSet<i32>,
    assignment: &HashMap<i32, bool>,
    symbol: i32,
    value: bool,
) -> (bool, HashMap<i32, bool>) {
    let mut new_symbols = symbols.clone();
    new_symbols.retain(|&s| s != symbol);
    let mut new_assignment = assignment.clone();
    new_assignment.insert(symbol, value);
    return dpll(cnf, &new_symbols, Some(new_assignment));
}

fn dpll(
    cnf: Vec<Vec<i32>>,
    symbols: &HashSet<i32>,
    input_assignment: Option<HashMap<i32, bool>>,
) -> (bool, HashMap<i32, bool>) {
    let assignment = input_assignment.unwrap_or_else(HashMap::new);

    // Return true if all clauses are satisfied
    if is_cnf_satisfied(&cnf, &assignment) {
        return (true, assignment);
    }
    // Check if there is a definitely unsatisfied clause
    if is_cnf_unsatisfied(&cnf, &assignment) {
        return (false, HashMap::new());
    }

    if cnf.is_empty() {
        return (true, assignment);
    }

    let (symbol, value) = find_pure_symbol(&cnf, symbols, &assignment);

    if let Some(symbol) = symbol {
        return dpll_with_assignment(cnf, symbols, &assignment, symbol, value.unwrap());
    }

    let (symbol, value) = find_unit_clause(&cnf, &assignment);

    if let Some(symbol) = symbol {
        return dpll_with_assignment(cnf, symbols, &assignment, symbol, value.unwrap());
    }

    let first_symbol = *symbols.iter().next().unwrap();
    let (result, new_assignment) = dpll_with_assignment(cnf.clone(), symbols, &assignment, first_symbol, true);
    if result {
        return (true, new_assignment);
    }
    return dpll_with_assignment(cnf, symbols, &assignment, first_symbol, false);
}

fn test_dpll() {
    // input, expected_result
    let inputs = vec![
        (vec![vec![1, 2], vec![1, -2]]), //true
        (vec![vec![1, 2], vec![-1, 2]]), //true
        (vec![vec![1, 2], vec![-1, -2]]), //true
        (vec![vec![1], vec![-1]]), //false
    ];
    let expected_results = vec![true, true, true, false];
    
    for (i, input) in inputs.iter().enumerate() {
        let cnf = input.clone();
        let symbols: HashSet<i32> = cnf.iter().flat_map(|clause| clause.iter().cloned().map(|lit: i32| lit.abs())).collect();
        let (result, _) = dpll(cnf, &symbols, None);
        assert_eq!(result, expected_results[i]);
    }
}

fn count_unsatisfied_clauses(cnf: &Vec<Vec<i32>>, assignment: &HashMap<i32, bool>) -> usize {
    cnf.iter()
        .filter(|clause| !is_clause_satisfied(clause, assignment))
        .count()
}

fn count_unsat_clauses_if_flipped(
    var: i32,
    cnf: &Vec<Vec<i32>>,
    assignment: &HashMap<i32, bool>,
) -> usize {
    let mut new_assignment = assignment.clone();
    new_assignment.insert(var, !new_assignment.get(&var).unwrap_or(&false));
    count_unsatisfied_clauses(cnf, &new_assignment)
}

fn get_vars(cnf: &Vec<Vec<i32>>) -> HashSet<i32> {
    cnf.iter()
        .flat_map(|clause| clause.iter().cloned().map(|lit| lit.abs()))
        .collect()
}

fn walk_sat(
    cnf: Vec<Vec<i32>>,
    rng: &mut ThreadRng,
    mut assignment: HashMap<i32, bool>,
    max_flips: usize,
    p: f64,
) -> (bool, HashMap<i32, bool>) {
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

fn random_cnf(num_vars: usize, num_clauses: usize) -> (Vec<Vec<i32>>, HashSet<i32>) {
    let mut rng = rand::thread_rng();
    let mut cnf = Vec::new();
    let symbols = (1..=num_vars as i32).collect();
    for _ in 0..num_clauses {
        let clause: Vec<i32> = (1..num_vars+1)
            .map(|var| {
                let sign = if rng.gen_bool(0.5) { 1 } else { -1 };
                sign * var as i32
            })
            .collect();
        cnf.push(clause);
    }
    (cnf, symbols)
}

fn proccess_combination(
    num_vars: usize,
    num_clauses: usize,
    algorithm: &str,
    rng: &mut ThreadRng,
) -> Vec<String> {
    let (cnf, symbols) = random_cnf(num_vars, num_clauses);
    let start = std::time::Instant::now();
    let (result, _) = if algorithm == "dpll" {
        dpll(cnf, &symbols, None)
    } else {
        walk_sat(cnf, rng, HashMap::new(), 100, 0.5)
    };
    let time = start.elapsed().as_secs_f64();
    let result_string = if result { "1" } else { "0" };
    vec![
        num_vars.to_string(),
        num_clauses.to_string(),
        time.to_string(),
        algorithm.to_string(),
        result_string.to_string(),
    ]
}

fn save_csv(data: Vec<Vec<String>>, filename: &str) {
    let mut wtr = csv::Writer::from_path(filename).unwrap();
    wtr.write_record(&["num_symbols", "num_clauses", "time", "algorithm", "solved"])
        .unwrap();
    for row in data {
        wtr.write_record(row).unwrap();
    }
    wtr.flush().unwrap();
}

fn main() {
    let test = false;
    if test {
        test_dpll();
        return;
    }
    let mut rng = rand::thread_rng();
    let mut results: Vec<Vec<String>> = Vec::new();
    let symbol_counts = (10..=100).step_by(2).collect::<Vec<usize>>();
    let clause_start = 1 as usize;
    let clause_end = 100 as usize;
    let rep_count = 100 as u64;
    let rep_count_size = rep_count as usize;
    let pb = ProgressBar::new(
        (symbol_counts.len() * (clause_end - clause_start) * rep_count_size) as u64,
    );
    pb.set_style(
        ProgressStyle::default_bar()
            .template(
                "{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta})",
            )
            .unwrap(),
    );
    for num_symbols in symbol_counts {
        for num_clauses in clause_start..=clause_end {
            for _ in 0..rep_count {
                results.push(proccess_combination(
                    num_symbols,
                    num_clauses,
                    "dpll",
                    &mut rng,
                ));
                results.push(proccess_combination(
                    num_symbols,
                    num_clauses,
                    "walksat",
                    &mut rng,
                ));
            }
            pb.inc(rep_count);
        }
    }
    save_csv(results, "results.csv");
}
