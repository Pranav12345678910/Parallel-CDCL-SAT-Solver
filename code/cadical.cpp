using namespace std;

#include <iostream>
#include <vector>
#include <string>
#include <random>
#include <algorithm>

struct AssInfo {
    int ass; // -1, 0, 1
    int level; // decision level, -1 if unassigned
    int reason; // idx of clause that forced it, -1 if none
    int saved;
};

void random_val(AssInfo& asss) {
    static std::mt19937 gen(std::random_device{}());
    std::bernoulli_distribution d(0.5);

    asss.ass = d(gen) ? 1 : -1;
}

void phase_val(AssInfo& asss) {
    asss.ass = asss.saved;
}

int simple_var(std::vector<AssInfo>& asses, int current_level, std::vector<int>& ass_order, std::vector<int>& ass_order_idxs) {
    int idx = 0;
    for (int i = 1; i < asses.size(); i++) {
        if (asses[i].ass == 0) {
            asses[i].level = current_level;
            asses[i].reason = -1;
            ass_order_idxs.push_back(ass_order.size());
            ass_order.push_back(i);
            idx = i;
            break;
        }
    }
    return idx;
}

int vsids_var(std::vector<AssInfo>& asses, int current_level, std::vector<int>& ass_order, std::vector<int>& ass_order_idxs, const std::vector<double>& activity) {
    int best_var = 0;
    double best_score = -1.0;

    for (int v = 1; v < asses.size(); v++) {
        if (asses[v].ass == 0 && activity[v] > best_score) {
            best_score = activity[v];
            best_var = v;
        }
    }

    if (best_var == 0) return 0;

    asses[best_var].level = current_level;
    asses[best_var].reason = -1;
    ass_order_idxs.push_back((int)ass_order.size());
    ass_order.push_back(best_var);

    return best_var;
}

int compute_backtrack_level(const std::vector<int>& clause,
                            const std::vector<AssInfo>& ass) {
    int highest = -1;
    int second = -1;

    for (int lit : clause) {
        int var = abs(lit);
        int lvl = ass[var].level;

        if (lvl > highest) {
            second = highest;
            highest = lvl;
        } else if (lvl > second && lvl < highest) {
            second = lvl;
        }
    }

    return std::max(0, second);
}

void backtrack(std::vector<AssInfo>& asses,
               std::vector<int>& ass_order,
               std::vector<int>& ass_order_idxs,
               int backtrack_level) {
    int keep = ass_order_idxs[backtrack_level + 1];

    for (int i = (int)ass_order.size() - 1; i >= keep; i--) {
        int var = ass_order[i];
        asses[var].ass = 0;
        asses[var].level = -1;
        asses[var].reason = -1;
    }

    ass_order.resize(keep);
    ass_order_idxs.resize(backtrack_level + 1);
}

int count_current_level_literals(const std::vector<int>& clause,
                                 const std::vector<AssInfo>& assignment,
                                 int current_level) {
    int count = 0;
    for (int lit : clause) {
        int var = abs(lit);
        if (assignment[var].level == current_level) {
            count++;
        }
    }
    return count;
}

int find_current_level_implied_literal(const std::vector<int>& clause,
                                       const std::vector<AssInfo>& assignment,
                                       int current_level) {
    for (int lit : clause) {
        int var = abs(lit);
        if (assignment[var].level == current_level &&
            assignment[var].reason != -1) {
            return var;
        }
    }
    return 0;
}

bool is_tautology(const std::vector<int>& clause) {
    for (int lit : clause) {
        if (std::find(clause.begin(), clause.end(), -lit) != clause.end()) {
            return true;
        }
    }
    return false;
}

std::vector<int> resolve(std::vector<int>& c1, std::vector<int>& c2, int var) {
    std::vector<int> res;

    for (int i = 0; i < c1.size(); i++) {
        int lit = c1[i];
        if (find(res.begin(), res.end(), lit) == res.end() && abs(lit) != var) {
            res.push_back(lit);
        }
    }

    for (int i = 0; i < c2.size(); i++) {
        int lit = c2[i];
        if (find(res.begin(), res.end(), lit) == res.end() && abs(lit) != var) {
            res.push_back(lit);
        }
    }

    if (is_tautology(res)) {
        std::cerr << "Tautological resolvent produced\n";
        exit(1);
    }

    return res;
}

int find_latest_current_level_implied_literal(const std::vector<int>& clause,
                                              const std::vector<int>& ass_order,
                                              const std::vector<int>& ass_order_idx,
                                              const std::vector<AssInfo>& assignment,
                                              int current_level) {
    int idx = ass_order_idx[current_level];
    for (int i = (int)ass_order.size() - 1; i >= idx; i--) {
        int var = ass_order[i];
        if (assignment[var].level == current_level && assignment[var].reason > -1) {
            for (int lit : clause) {
                if (abs(lit) == var) {
                    return var;
                }
            }
        }
    }
    return 0;
}

int UnitProp(std::vector<int>& ass_order, std::vector<std::vector<int>>& watch_pointers, 
             std::vector<std::vector<int>>& formula, std::vector<AssInfo>& assignment, int current_level, int &qhead) {

    

    while (qhead < ass_order.size()) {


        // get list of clauses that are watching the top literal on the queue  
        int var = ass_order[qhead];
        qhead++;
        int val = assignment[var].ass;
        int lit = -(var * val);
        int idx = (abs(lit) * 2) + (lit < 0 ? 1 : 0);
        std::vector<int>& watches = watch_pointers[idx];

        int i = 0;
        int j = 0;

        // iterate through the clauses watching this literal
        while (i < watches.size()) {

            int clause_idx = watches[i];
            std::vector<int>& current_clause = formula[clause_idx];
            if (current_clause[0] == lit) {
                swap(current_clause[0], current_clause[1]);
            }

            // at this point, we know current_clause[1] is the False one 
            int var2 = abs(current_clause[0]);
            int value_to_sat = (current_clause[0] > 0) ? 1 : -1;

            if (assignment[var2].ass == value_to_sat) {
                // we know the clause is satisfied, so there is no need to modify its watch pointers
                watches[j] = watches[i];
                j++;
                i++;
                continue;
            }

            // we want to swap the one we know is false (current_clause[1]) with some other one that isn't 
            bool found_new_watch = false;
            for (int index = 2; index < current_clause.size(); index ++) {
                var2 = abs(current_clause[index]);
                value_to_sat = (current_clause[index] > 0) ? 1 : -1;
                if (assignment[var2].ass != -value_to_sat) {
                    swap(current_clause[1], current_clause[index]);
                    int watch_list_idx = (abs(current_clause[1]) * 2) + (current_clause[1] < 0 ? 1 : 0);
                    watch_pointers[watch_list_idx].push_back(clause_idx);
                    found_new_watch = true;
                    i++;
                    break;
                }
            }

            // if we were unable to find a non-false one
            if (!found_new_watch) {
                watches[j++] = watches[i++];
                var2 = abs(current_clause[0]);
                value_to_sat = (current_clause[0] > 0) ? 1 : -1;
                if (assignment[var2].ass == -value_to_sat) {
                    // conflict, because we cant find anything that is not false
                    while (i < watches.size()) {
                        watches[j] = watches[i];
                        j++;
                        i++;
                    }
                    watches.resize(j);
                    return clause_idx;
                }
                // unassigned
                if (assignment[var2].ass == 0) {
                    // do unit propagation to make the clause true
                    assignment[var2].ass = value_to_sat;
                    assignment[var2].level = current_level;
                    assignment[var2].reason = clause_idx;
                    ass_order.push_back(var2); 
                }
            }

        }

        watches.resize(j);

    }

    return -1;


}

std::vector<int> learn(std::vector<int>& ass_order, std::vector<int>& ass_order_idx, std::vector<AssInfo>& assignment, int conflict, std::vector<std::vector<int>>& formula, int current_level) {
    std::vector<int> conflict_clause = formula[conflict];

    while (count_current_level_literals(conflict_clause, assignment, current_level) > 1) {
        int var = find_latest_current_level_implied_literal(conflict_clause, ass_order, ass_order_idx, assignment, current_level);
        AssInfo assInfo = assignment[var];
        std::vector<int> reason_clause = formula[assInfo.reason];
        conflict_clause = resolve(reason_clause, conflict_clause, var);
    }

    if (conflict_clause.size() > 1) {
        for (int i = 0; i < conflict_clause.size(); i++) {
            int var = abs(conflict_clause[i]);
            if (assignment[var].level == current_level) {
                swap(conflict_clause[0], conflict_clause[i]);
                break;
            }
        }
        int highest_other_level = -1;
        int best_index = 1;
        for (int i = 1; i <     conflict_clause.size(); i++) {
            int var = abs(conflict_clause[i]);
            if (assignment[var].level > highest_other_level) {
                highest_other_level = assignment[var].level;
                best_index = i;
            }
        }
        swap(conflict_clause[1], conflict_clause[best_index]);
    }

    return conflict_clause;
}

std::vector<bool> solve(int num_variables, std::vector<std::vector<int>>& formula) {
    // -1 means false, 1 means true, 0 means unassigned
    // std::vector<int> assignment(num_variables + 1, 0);

    // watch pointers list. for each literal, list of clause indices watching it
    std::vector<std::vector<int>> watch_pointers(num_variables * 2 + 2);

    // indicates clause that, through unit propagation, led to each variables assignment
    // std::vector<int> reason(num_variables + 1, -1);   

    // we need to know how each variable got assigned to do backtracking 
    // std::vector<int> level(num_variables + 1, -1);  

    std::vector<AssInfo> assignment(num_variables + 1, AssInfo{0, -1, -1, -1});


    std::vector<int> ass_order;
    std::vector<int> ass_order_idxs;
    ass_order_idxs.push_back(0);


    int current_level = 0;
    int qhead = 0;

    std::vector<double> activity(num_variables + 1, 0.0);

    std::string var_heuristic = "simple";
    std::string val_heuristic = "random";

    for (int i = 0; i < formula.size(); i ++) {
        if (formula[i].size() == 0) {
            return {};
        }
        else if (formula[i].size() > 1) {
            int lit0 = formula[i][0];
            int lit1 = formula[i][1];
            int watch_list_idx_0 = abs(lit0 * 2) + (lit0 < 0 ? 1 : 0);
            int watch_list_idx_1 = abs(lit1 * 2) + (lit1 < 0 ? 1 : 0);
            watch_pointers[watch_list_idx_0].push_back(i);
            watch_pointers[watch_list_idx_1].push_back(i);
        }
        else if (formula[i].size() == 1) {
            int lit = formula[i][0];
            int var = abs(lit);
            int val = (lit > 0) ? 1 : -1;


            // if there is a contradiction enforced by a unit clause, it won't be detected by watch pointers
            // so we have to check if we have already assigned it to be false and immediately return unsat if so
            if (assignment[var].ass == -val) {
                return {}; 
            } 

            if (assignment[var].ass == 0) {
                assignment[var].ass = val;
                assignment[var].level = current_level;
                assignment[var].reason = i;
                ass_order.push_back(var);
            }   
        }

    }
    
    int conflict = UnitProp(ass_order, watch_pointers, formula, assignment, current_level, qhead);

    if (conflict != -1) {
        return {};
    }

    while (true) {
        current_level++;
        int l;
        if (var_heuristic == "simple") {
            l = simple_var(assignment, current_level, ass_order, ass_order_idxs);
        } else if (var_heuristic == "vsids") {
            l = vsids_var(assignment, current_level, ass_order, ass_order_idxs, activity);
        }

        if (l == 0) {
            std::vector<bool> final_assignment(num_variables + 1);
            for (int i = 1; i <= num_variables; i++) {
                final_assignment[i] = (assignment[i].ass == 1);
            }
            return final_assignment;
        } 

        if (val_heuristic == "random") {
            random_val(assignment[l]);
        } else if (val_heuristic == "phase") {
            phase_val(assignment[l]);
        } 

        conflict = UnitProp(ass_order, watch_pointers, formula, assignment, current_level, qhead);

        // incorporate l into our assignment            
        while (conflict != -1) {

            // this is better than checking if newClause is empty after cause it's more efficient
            if (current_level == 0) {
                return {}; 
            }

            std::vector<int> newClause = learn(ass_order, ass_order_idxs, assignment, conflict, formula, current_level);
            int backtrack_level = compute_backtrack_level(newClause, assignment);


            formula.push_back(newClause);

            // we have to change our watch pointers data structure to watch up to two things in this new clause
            int new_clause_idx = formula.size() - 1;

            int idx_0 = (abs(newClause[0]) * 2) + (newClause[0] < 0 ? 1 : 0);

            if (newClause.size() > 1) {
                int idx_1 = (abs(newClause[1]) * 2) + (newClause[1] < 0 ? 1 : 0);
                watch_pointers[idx_0].push_back(new_clause_idx);
                watch_pointers[idx_1].push_back(new_clause_idx);
            }            
           
            backtrack(assignment, ass_order, ass_order_idxs, backtrack_level);

            current_level = backtrack_level;
            qhead = ass_order.size();

            // assume newClause[0] is unassigned
            int value_to_sat = (newClause[0] > 0) ? 1 : -1;
            int new_var = abs(newClause[0]);
            assignment[new_var].ass = value_to_sat; 
            assignment[new_var].level = current_level;
            assignment[new_var].reason = new_clause_idx;
            assignment[new_var].saved = value_to_sat;
            ass_order.push_back(new_var);
            conflict = UnitProp(ass_order, watch_pointers, formula, assignment, current_level, qhead);
        }
    }

}


int main() {
    // 1. Define a tiny test problem
    // Let's use 3 variables: A=1, B=2, C=3
    int num_variables = 30;

    // 2. Create the formula (CNF)
    // Clause 1: (A or B)       -> {1, 2}
    // Clause 2: (Not A or C)   -> {-1, 3}
    // Clause 3: (Not B or Not C) -> {-2, -3}

    std::vector<std::vector<int>> formula = {

        // Each pigeon in at least one hole
        {1,2,3,4,5},
        {6,7,8,9,10},
        {11,12,13,14,15},
        {16,17,18,19,20},
        {21,22,23,24,25},
        {26,27,28,29,30},

        // No pigeon in two holes
        {-1,-2},{-1,-3},{-1,-4},{-1,-5},{-2,-3},{-2,-4},{-2,-5},{-3,-4},{-3,-5},{-4,-5},
        {-6,-7},{-6,-8},{-6,-9},{-6,-10},{-7,-8},{-7,-9},{-7,-10},{-8,-9},{-8,-10},{-9,-10},
        {-11,-12},{-11,-13},{-11,-14},{-11,-15},{-12,-13},{-12,-14},{-12,-15},{-13,-14},{-13,-15},{-14,-15},
        {-16,-17},{-16,-18},{-16,-19},{-16,-20},{-17,-18},{-17,-19},{-17,-20},{-18,-19},{-18,-20},{-19,-20},
        {-21,-22},{-21,-23},{-21,-24},{-21,-25},{-22,-23},{-22,-24},{-22,-25},{-23,-24},{-23,-25},{-24,-25},
        {-26,-27},{-26,-28},{-26,-29},{-26,-30},{-27,-28},{-27,-29},{-27,-30},{-28,-29},{-28,-30},{-29,-30},

        // No two pigeons share a hole
        {-1,-6},{-1,-11},{-1,-16},{-1,-21},{-1,-26},{-6,-11},{-6,-16},{-6,-21},{-6,-26},{-11,-16},{-11,-21},{-11,-26},{-16,-21},{-16,-26},{-21,-26},
        {-2,-7},{-2,-12},{-2,-17},{-2,-22},{-2,-27},{-7,-12},{-7,-17},{-7,-22},{-7,-27},{-12,-17},{-12,-22},{-12,-27},{-17,-22},{-17,-27},{-22,-27},
        {-3,-8},{-3,-13},{-3,-18},{-3,-23},{-3,-28},{-8,-13},{-8,-18},{-8,-23},{-8,-28},{-13,-18},{-13,-23},{-13,-28},{-18,-23},{-18,-28},{-23,-28},
        {-4,-9},{-4,-14},{-4,-19},{-4,-24},{-4,-29},{-9,-14},{-9,-19},{-9,-24},{-9,-29},{-14,-19},{-14,-24},{-14,-29},{-19,-24},{-19,-29},{-24,-29},
        {-5,-10},{-5,-15},{-5,-20},{-5,-25},{-5,-30},{-10,-15},{-10,-20},{-10,-25},{-10,-30},{-15,-20},{-15,-25},{-15,-30},{-20,-25},{-20,-30},{-25,-30}
    };

    std::cout << "Starting CDCL Solver..." << std::endl;

    std::vector<bool> result = solve(num_variables, formula);

    if (result.empty()) {
        std::cout << "\nResult: UNSATISFIABLE" << std::endl;
    } else {
        std::cout << "\nResult: SATISFIABLE!" << std::endl;
        std::cout << "Assignment:" << std::endl;
        
        for (int i = 1; i <= num_variables; i++) {
            std::cout << "Var " << i << " = " 
                      << (result[i] ? "True (1)" : "False (-1)") << std::endl;
        }
    }

    return 0;
}