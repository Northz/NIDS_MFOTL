import argparse
import random
import os
import numpy as np
import re

parser = argparse.ArgumentParser()
parser.add_argument('--output',
                    help='Output path', required=True)
parser.add_argument('--formula',
                    help='The formula file', required=True)
parser.add_argument('--pattern',
                    help="Sets the pattern of the log. Possible values: since, historically, once", required=True)
parser.add_argument('--length',
                    help="Sets the length of the log. Default value: 10000")

args = parser.parse_args()

output = args.output
formula_path = args.formula
length = args.length or 10000
pattern = args.pattern


length = int(length)


def write_file(f, text):
    with open(f, "w") as text_file:
        text_file.write(text)


def read_file(filename):
    with open(filename) as f:
        content = f.read()

    return content


def read_lines(filename):
    with open(filename) as f:
        content = f.read().splitlines()

    return content


def insert_variables(formula, variables):
    for variable in variables:
        formula = formula.replace(variable, str(variables[variable]))
    return formula


formula = read_file(os.path.join(formula_path)).strip()
if "AND" in formula:
    formula = re.split("\sAND\s", formula)[1][1:-1]


interval = re.findall(r'\[\d+,(?:\*|\d+)\]', formula)[0][1:-1].split(",")
if (int(interval[0]) > length):
    print(
        f'The interval lower bound ({interval[0]}) is larger than the requested log length ({str(length)})!')
    exit()


subformulas = re.split(r'\sTRIGGER\[\d+,(?:\*|\d+)\]\s', formula)
lhs = subformulas[0][1:-1]
rhs = subformulas[1][1:-1]

lhs_predicates = []
rhs_predicates = []

if not(lhs in ["TRUE", "FALSE"]):
    lhs_predicates.append(lhs)

if not(rhs in ["TRUE", "FALSE"]):
    rhs_predicates.append(rhs)

predicates = lhs_predicates + rhs_predicates

log = []

print("Generating log of length " + str(length))

variables = ["x", "y"]


def generate_assignments():
    assignments = []

    values_x = range(0, random.randint(1, 10))
    values_y = range(0, random.randint(1, 10))

    for val_x in values_x:
        for val_y in values_y:
            assignment = {
                "x": val_x,
                "y": val_y
            }
            assignments.append(assignment)

    return assignments


def append_to_log(log, t, preds, assignments, additional_assignments=[]):
    log.append(
        "@" + str(t) + " " + " ".join(list(set([insert_variables(p, a) for p in preds for a in assignments] + [insert_variables(p, a) for p in predicates for a in additional_assignments]))))


i = 0
t = 0

# independent of the pattern, the first length-b entries can be filled with random values for I = [a, b]
if not(interval[1] == "*"):
    while i < length - (int(interval[1])):

        # additional assignments, just s.t. the log isn't perfectly uniform
        assignments = generate_assignments()

        if random.uniform(0, 1) < 0.1:
            t = t+1

        append_to_log(log, t, predicates, assignments)

        i = i+1

# the remainder of the log follows a pattern

if pattern == "historically":

    # one assignment for all entries. at least rhs
    assignments = generate_assignments()

    # print("The historically assignments are")
    # print(assignments)

    while i < length - (int(interval[0])):

        # additional assignments, just s.t. the log isn't perfectly uniform
        additional_assignments = generate_assignments()

        if random.uniform(0, 1) < 0.1:
            t = t+1

        append_to_log(log, t, rhs_predicates,
                      assignments, additional_assignments)

        i = i+1

    # last a entries are random for interval I = [a, b]
    while i < length:

        assignments = generate_assignments()

        if random.uniform(0, 1) < 0.1:
            t = t+1

        append_to_log(log, t, predicates, assignments)

        i = i+1

elif pattern == "since":
    # choose a log index where phi / the lhs occurs. must be within the interval!
    loc = random.randint(0, length - (int(interval[0])))

    # print("place rhs of since at " + str(loc))

    # up to that location, generate random entries
    while i < loc:

        assignments = generate_assignments()

        if random.uniform(0, 1) < 0.1:
            t = t+1

        append_to_log(log, t, predicates, assignments)

        i = i+1

    # add the entry for the lhs AND rhs for given assignments
    assignments = generate_assignments()
    append_to_log(log, t, predicates, assignments)

    i = i+1

    # from there on only generate rhs with the at least same assignments until the end of the interval is reached
    while i < length - (int(interval[0])):
        # additional assignments, just s.t. the log isn't perfectly uniform
        additional_assignments = generate_assignments()

        if random.uniform(0, 1) < 0.1:
            t = t+1

        append_to_log(log, t, rhs_predicates,
                      assignments, additional_assignments)
        i = i+1

    # [0, a-1] can again be filled with random assignments
    while i < length:
        assignments = generate_assignments()

        if random.uniform(0, 1) < 0.1:
            t = t+1

        append_to_log(log, t, predicates, assignments)
        i = i+1

    pass
elif pattern == "once":

    if interval[0] == "0":
        print("For pattern 'once', the lower bound of the intervall cannot be 0!")
        exit(0)

    # first few entries are completely random
    while i < length - (int(interval[0])):

        assignments = generate_assignments()

        if random.uniform(0, 1) < 0.1:
            t = t+1

        append_to_log(log, t, predicates, assignments)

        i = i+1

    # last a entries are (almost) random as well
    log_end = []
    while i < length:

        assignments = generate_assignments()

        if random.uniform(0, 1) < 0.1:
            t = t+1

        append_to_log(log_end, t, predicates, assignments)

        i = i+1
    # but the last a entries contain one occurence of the lhs
    assignments = generate_assignments()
    idx = random.randint(0, len(log_end) - 1)
    t_once = re.findall(r'@\d+\s', log_end[idx])[0][1:-1]
    log_end[idx] = "@" + str(t_once) + " " + " ".join(
        list(set([insert_variables(p, a) for p in lhs_predicates for a in assignments])))

    log = log + log_end

write_file(os.path.join(output), "\n".join(log) + "\n")
