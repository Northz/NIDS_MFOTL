import argparse
import random
import os
import numpy as np

parser = argparse.ArgumentParser()
parser.add_argument('--output-dir',
                    help='Output directory', required=True)
parser.add_argument('--signature',
                    help='The signature file', required=True)
parser.add_argument('--min-length',
                    help="Sets the minimum length of the log. Default value: 10000")
parser.add_argument('--max-length',
                    help="Sets the maximum length of the log. Default value: 100000")
parser.add_argument('--min-trigger-length',
                    help="Sets the minimum length of a trigger sequence. Default value: 10")
parser.add_argument('--max-trigger-length',
                    help="Sets the maximum length of a trigger sequence. Default value: --max-length")
parser.add_argument('--time-increase-probability',
                    help="Sets probability for the time to increase. Default value: 0.1")
parser.add_argument('--max-predicate-variables',
                    help="Sets the maximum number of a variables per predicate per log entry. Default value: 10")

args = parser.parse_args()

output_dir = args.output_dir
signature_path = args.signature
min_length = args.min_length or 10000
max_length = args.max_length or 100000
min_trigger_length = args.min_trigger_length or 10
max_trigger_length = args.max_trigger_length or max_length
time_increase_probability = args.time_increase_probability or 0.1
max_predicate_variables = args.max_predicate_variables or 10

min_length = int(min_length)
max_length = int(max_length)
min_trigger_length = int(min_trigger_length)
max_trigger_length = int(max_trigger_length)
time_increase_probability = float(time_increase_probability)
max_predicate_variables = int(max_predicate_variables)


def write_file(f, text):
    with open(f, "w") as text_file:
        text_file.write(text)


def read_lines(filename):
    with open(filename) as f:
        content = f.read().splitlines()

    return content


length = random.randint(min_length, max_length)
i = 0
t = 0

signature_lines = read_lines(os.path.join(signature_path))

predicates = [pred[0] for pred in signature_lines]

log = []

print("Generating log of length " + str(length) +
      " using " + str(len(predicates)) + " predicate(s).")

while i < length:
    if min(max_trigger_length, length - i) < min_trigger_length:
        break

    trigger_length = random.randint(
        min_trigger_length, min(max_trigger_length, length - i))
    number_of_predicates = random.randint(1, len(predicates))
    preds = random.sample(predicates, number_of_predicates)
    vars = random.randint(1, max_predicate_variables)

    #print("Generating trigger sequence of length " + str(trigger_length) + ", " + str(number_of_predicates) + " predicate(s) with " + str(vars) + " variables each...")

    for j in range(0, trigger_length):
        if random.uniform(0, 1) < time_increase_probability:
            t = t+1

        log.append(
            "@" + str(t) + " " + " ".join([p + "(" + str(v) + ")" for p in predicates for v in range(0, vars)]))

    i += trigger_length

write_file(os.path.join(output_dir, "log.txt"), "\n".join(log) + "\n")
