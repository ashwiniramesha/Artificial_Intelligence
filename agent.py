#!/usr/bin/python
import re

assertion_tuples_list = []
assertions = []
assertion_obj_map = {}
implications = []
implication_map = {}
rules = []
query = ""


def prepare_assertions():
    global assertions
    global assertion_obj_map

    for rule in rules:

        is_assertion = rule.find('&')

        is_implication = rule.find('=>')

        if is_assertion < 0 and is_implication < 0:
            assertions.append(rule)

    for assertion in assertions:
        assertion = assertion.strip(' ')
        split_assertion = assertion.split('(')
        predicate = split_assertion[0]
        constants = split_assertion[1].strip('()').split(',')
        assertion_tuples_list.append((predicate,constants))
        #assertion_obj_map[predicate] = constants

def prepare_implications():
    global implications
    global implication_map

    for rule in rules:

        is_implication = rule.find('=>')
        if is_implication > 0:
            implications.append(rule)

    for implication in implications:
        consequence_predicate_map = {}
        implication = implication.strip(' ')
        split_implication = implication.split('=>')
        premise = split_implication[0].strip(' ')
        consequence = split_implication[1].strip(' ')
        split_consequence = consequence.split('(')
        get_objects = split_consequence[1].strip(')')
        obj_list = get_objects.split(',')
        consequence_predicate_map[split_consequence[0]] = obj_list

        premise_conjuncts = premise.split('&')

        implication_map[implication] = (premise,consequence_predicate_map,premise_conjuncts)

        

def read_input():
    global query
    global rules

    input_file = open("input.txt","r")
    input_lines = input_file.readlines()

    raw_query_clause = input_lines[0].strip("\n")
    query = re.sub(r'\s+','',raw_query_clause)
    num_of_rules = int(input_lines[1].strip("\n"))

    for i in range(0,num_of_rules):
        raw_rule = input_lines[i+2].strip("\n")
        trimmed_rule = re.sub(r'\s+','',raw_rule)
        rules.append(trimmed_rule)
    input_file.close()


def fetch_rules_for_goal(KB, goal):
    goal_predicate = goal.split('(')[0] 
    matching_rules = []
    
    for rule in rules:
        if '=>' in rule:
            rule_consequence = rule.split('=>')[1]
        else:
            rule_consequence = rule
        
        rule_conseq_predicate = rule_consequence.split('(')[0]
        rule_objs = rule_consequence.split('(')[1]
        trim_rule_objs = rule_objs.strip('()')
        list_of_obj_rule = trim_rule_objs.split(',')
        goal_objs = goal.split('(')[1]
        trim_goal_obj = goal_objs.strip('()')
        list_of_obj_goal = trim_goal_obj.split(',')
        
        if goal_predicate == rule_conseq_predicate:
            count = 0
            if len(list_of_obj_goal)== len(list_of_obj_rule):
                if list_of_obj_goal == list_of_obj_rule:
                     matching_rules.append(rule)
                else:
                    for index in range(0,len(list_of_obj_rule)):
                        if list_of_obj_goal[index] == list_of_obj_rule[index]:
                            count = count+1
                        elif list_of_obj_goal[index] == 'x' or list_of_obj_rule[index] == 'x':
                            count = count+1
                        
                    if count == len(list_of_obj_rule):
                        matching_rules.append(rule)
                    
                        

    return matching_rules 

def is_list(entity):
    entity_type = type(entity)
    if 'list' in str(entity_type):
        return True
    else:
        return False 

def is_compound(entity):
    if '(' in entity:
        return True
    else:
        return False

def get_args(entity):
    split_args = entity.split('(')
    arg_string = split_args[1].strip('()')
    args = arg_string.split(',') 
    return args

def unify(x,y,theta):
    if theta == "FAIL":
        return "FAIL"

    elif x == y:
        return theta

    elif not is_list(x) and not is_list(y) and not is_compound(x) and not is_compound(y) and x != 'x' and y != 'x':
        return "FAIL"
 
    elif x == 'x': 
        return unify_var(x,y,theta)

    elif y == 'x':
        return unify_var(y,x,theta)

    elif is_compound(x) and is_compound(y):
        x_predicate = x.split('(')[0] 
        y_predicate = y.split('(')[0] 
        x_args = get_args(x)
        y_args = get_args(y)
        
        return unify(x_args, y_args, unify(x_predicate, y_predicate, theta))

    elif is_list(x) and is_list(y) and len(x) == len(y):
        x_rest = x[1:]
        y_rest = y[1:]
        return unify(x_rest, y_rest, unify(x[0], y[0], theta))

    else:
        return "FAIL"

def unify_var(var,x,theta):
    if var in theta  and theta[var]== x: 
        return unify(theta[var], x, theta)

    elif x in theta:
        return unify(var, theta[x], theta)

    else:
        theta[var] = x 
        return theta


def FIRST(goals):
    separated_goals = []
    if '&' in goals:
        separated_goals.extend(goals.split('&'))
        return separated_goals[0]
    return goals


def REST(goals):
    separated_goals = []
    if '&' in goals:
        separated_goals.extend(goals.split('&'))
        separated_goals.pop(0)
        return '&'.join(separated_goals)
    return "" 

def ask_generator(query):
    return FOL_BC_ASK(rules,query)

def ask(query):
        """Return a substitution that makes the query true, or,
        failing that, return False."""
        for result in ask_generator(query):
            return result
        return "FAIL"

def FOL_BC_ASK(rules, query):
    theta = {} 
    return FOL_BC_OR(rules, query, theta)


def subst(theta, x):
    new_arg = []
    predicate = x.split('(')[0]
    args = x.split('(')[1]
    trimmed_args = args.strip('()')
    arg_list = trimmed_args.split(',')
    for arg in arg_list:
        if arg in theta:
            new_arg.append(theta[arg])
        else:
            new_arg.append(arg)

    new_x = predicate+'('+",".join(new_arg)+')' 
    return new_x


def FOL_BC_OR(rules, goal, theta):
    goal_predicate = goal.split('(')[0] 
    goal_objs = goal.split('(')[1]
    trim_goal_obj = goal_objs.strip('()')
    goal_obj_list = trim_goal_obj.split(',')

    matching_rules = []
    
    matching_rules = fetch_rules_for_goal(rules, goal)
    if len(matching_rules) == 0:
        no_matches = unify(goal, matching_rules, "FAIL")
        yield no_matches 

    for i in range(0,len(matching_rules)):

        is_assertive = False
        if '=>' in matching_rules[i]:
            rule_consequence = matching_rules[i].split('=>')[1]
        else:
            is_assertive = True
            rule_consequence = matching_rules[i]
        
        rule_conseq_predicate = rule_consequence.split('(')[0]
        
        if goal_predicate == rule_conseq_predicate:
            if is_assertive == True:
                rule_premise = ''
            else:
                rule_premise = matching_rules[i].split('=>')[0] 

        for theta1 in FOL_BC_AND(rules, rule_premise, unify(rule_consequence, goal, theta)):
            if theta1 == "FAIL":
               continue
 
            yield theta

    list_exhausted = unify(goal, [], "FAIL")
    yield list_exhausted


def FOL_BC_AND(KB, goals, theta):
    if theta == "FAIL":
        yield theta 

    elif len(goals) == 0:
        yield theta 

    else:
        first = FIRST(goals)
        rest = REST(goals)
        for theta1 in FOL_BC_OR(rules,subst(theta, first),theta):
            if theta1 == "FAIL":
                #theta = {}
                continue
            for theta2 in FOL_BC_AND(rules, rest, theta1):
                if theta2== "FAIL":
                    continue
                yield theta2


read_input()
#filter assertions from the set of rules read from input.
prepare_assertions()

#filter implications from the set of rules read from input.
prepare_implications()
result = ask(query)

out_file = open("output.txt","w")

if result == "FAIL":
    final_result = "FALSE"
else:
    final_result = "TRUE"

out_file.write(final_result)
out_file.close()
