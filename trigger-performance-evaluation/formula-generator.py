import argparse
import random
import os
import numpy as np

formulas = [
    "TERMINAL",
    "OR",
    "AND",
    # "PREV",
    # "NEXT",
    # "SINCE",
    # "UNTIL",
    # "NOT", makes most things unsafe
]

parser = argparse.ArgumentParser()
parser.add_argument('--output-dir',
                    help='Output directory', required=True)
parser.add_argument('--min-depth',
                    help="Sets the minimum (recursive) depth of the formula. Default value: 1")
parser.add_argument('--max-depth',
                    help="Sets the maximum (recursive) depth of the formula. Default value: 5")
parser.add_argument('--min-predicates',
                    help="Sets the minimum number of predicates. Default value: 0")
parser.add_argument('--max-predicates',
                    help="Sets the maximum number of predicates. Default value: 5")
parser.add_argument('--max-interval-bound',
                    help="Sets the maximum interval bound. Default value: 10000")
parser.add_argument('--interval-mean',
                    help="Sets the mean for the interval bound normal distribution. Default value: 1000")
parser.add_argument('--interval-var',
                    help="Sets the variance for the interval bound normal distribution. Default value: 500")
parser.add_argument('--new-predicate-probability',
                    help="Sets the probability of a new predicate being introduced. Default value: 0.5")
parser.add_argument('--type',
                    help="Sets the type of the generated formula Possible values: 0, bounded, unbounded. Default value: 0")

args = parser.parse_args()

output_dir = args.output_dir
min_depth = args.min_depth or 1
max_depth = args.max_depth or 5
min_predicates = args.min_predicates or 0
max_predicates = args.max_predicates or 5
max_interval_bound = args.max_interval_bound or 10000
interval_mean = args.interval_mean or 1000
interval_var = args.interval_var or 500
new_predicate_probability = args.new_predicate_probability or 0.5
type = args.type or "0"

min_depth = int(min_depth)
max_depth = int(max_depth)
min_predicates = int(min_predicates)
max_predicates = int(max_predicates)
max_interval_bound = int(max_interval_bound)
interval_mean = int(interval_mean)
interval_var = int(interval_var)
new_predicate_probability = float(new_predicate_probability)

if not(os.path.isdir(output_dir)):
    os.makedirs(output_dir)


def next_uppercase(string):
    char = ord(string[-1])
    if char == 90:
        # the last character is a 'Z', full circle back to 'A'
        return string + "A"
    else:
        return string[:-1] + chr(char+1)


def generate_interval_bound(maximum=max_interval_bound, minimum=0):
    x = np.random.normal(interval_mean, interval_var, 1)
    return min(max(int(x), minimum), maximum)


def generate_interval(allow_unbounded=True):

    if allow_unbounded and random.uniform(0, 1) >= 0.5:
        right_bound = "*"
        left_bound = generate_interval_bound()
    else:
        right_bound = generate_interval_bound()
        left_bound = generate_interval_bound(right_bound)

    return [str(left_bound), str(right_bound)]


def flip_int(I):
    return [str(int(I[1]) + 1), "*"]


def flip_int_less_lower(I):
    return ["0", str(int(I[0]) - 1)]


def int_remove_lower_bound(I):
    return ["0", I[1]]


def int_all():
    return ["0", "*"]


def f_FALSE():
    return f'FALSE'


def f_TRUE():
    return f'TRUE'


def f_NOT(f):
    return f'NOT ({f})'


def f_OR(f1, f2):
    return f'({f1}) OR ({f2})'


def f_AND(f1, f2):
    return f'({f1}) AND ({f2})'


def f_PREV(I, f):
    return f'PREV[{",".join(I)}] ({f})'


def f_NEXT(I, f):
    return f'NEXT[{",".join(I)}] ({f})'


def f_SINCE(f1, I, f2):
    return f'({f1}) SINCE[{",".join(I)}] ({f2})'


def f_UNTIL(f1, I, f2):
    return f'({f1}) UNTIL[{",".join(I)}] ({f2})'


def f_TRIGGER(f1, I, f2):
    return f'({f1}) TRIGGER[{",".join(I)}] ({f2})'


def f_FIRST():
    return f_NOT(f_PREV(int_all(), f_TRUE()))


def f_ONCE(I, f):
    return f_SINCE(f_TRUE(), I, f)


def f_EVENTUALLY(I, f):
    return f_UNTIL(f_TRUE(), I, f)


def f_HIST_SAFE_0(I, f):
    if(I[1] == "*"):
        return f_SINCE(f, I, f_AND(f_FIRST(), f))
    else:
        return f_OR(f_SINCE(f, flip_int(I), f_NEXT(int_all(), f)), f_SINCE(f, I, f_AND(f_FIRST(), f)))


def f_HIST_SAFE_UNBOUNDED(I, f):
    return f_AND(
        f_ONCE(
            flip_int_less_lower(I),
            f_PREV(
                int_all(),
                f_SINCE(
                    f,
                    int_all(),
                    f_AND(
                        f,
                        f_FIRST()
                    )
                )
            )
        ),
        f_ONCE(I, f)
    )


def f_HIST_SAFE_BOUNDED(I, f):
    return f_AND(
        f_ONCE(I, f),
        f_NOT(
            f_ONCE(
                I,
                f_AND(
                    f_OR(
                        f_ONCE(
                            int_remove_lower_bound(I),
                            f
                        ),
                        f_EVENTUALLY(
                            int_remove_lower_bound(I),
                            f
                        )
                    ),
                    f_NOT(f)
                )
            )
        )
    )


def f_TRIGGER_SAFE_0(f1, I, f2):
    return f_OR(
        f_SINCE(f2, I, f_AND(f2, f1)),
        f_HIST_SAFE_0(I, f2)
    )


def f_TRIGGER_SAFE_UNBOUNDED(f1, I, f2):
    return f_AND(
        f_ONCE(I, f_TRUE()),
        f_OR(
            f_OR(
                f_HIST_SAFE_UNBOUNDED(I, f2),
                f_ONCE(flip_int_less_lower(I), f1)
            ),
            f_ONCE(
                flip_int_less_lower(I),
                f_PREV(
                    int_all(),
                    f_SINCE(
                        f2,
                        int_remove_lower_bound(I),
                        f_AND(f1, f2)
                    )
                )
            )
        )
    )


def f_TRIGGER_SAFE_BOUNDED(f1, I, f2):
    return f_AND(
        f_ONCE(I, f_TRUE()),
        f_OR(
            f_OR(
                f_HIST_SAFE_BOUNDED(I, f2),
                f_ONCE(flip_int_less_lower(I), f1)
            ),
            f_ONCE(
                flip_int_less_lower(I),
                f_PREV(
                    int_all(),
                    f_SINCE(
                        f2,
                        int_remove_lower_bound(I),
                        f_AND(f1, f2)
                    )
                )
            )
        )
    )


def generate_formula_aux(f, depth, predicates=[], allow_new_predicates=True):
    if f == "TERMINAL":
        # most of the time generate a predicate, sometimes TRUE / FALSE
        terminal = random.uniform(0, 1)
        if terminal < 0.1:
            return f_FALSE(), predicates, depth
        elif terminal < 0.2:
            return f_TRUE(), predicates, depth
        else:
            new_predicate = random.uniform(0, 1)
            if len(predicates) == 0:
                if allow_new_predicates:
                    # first predicate
                    predicate = "A", ["a"]
                    predicates = predicates + [predicate]
                else:
                    # simply return True, no (new) predicates can be generated
                    return f_TRUE(), predicates, depth
            elif new_predicate < new_predicate_probability and len(predicates) < max_predicates and allow_new_predicates:
                # generate a new predicate
                pred, vars = predicates[-1]
                string = next_uppercase(pred)
                predicate = string, [string.lower()]
                predicates = predicates + [predicate]
            else:
                # use an existing predicate
                predicate = predicates[random.randint(0, len(predicates)-1)]

            pred, vars = predicate
            return pred + " (" + ",".join(vars) + ")", predicates, depth
    elif f == "OR":
        f1, predicates, d1 = generate_formula(
            depth+1, predicates, allow_new_predicates)
        f2, predicates, d2 = generate_formula(
            depth+1, predicates, allow_new_predicates)
        return f_OR(f1, f2), predicates, max(d1, d2)
    elif f == "AND":
        f1, predicates, d1 = generate_formula(
            depth+1, predicates, allow_new_predicates)
        f2, predicates, d2 = generate_formula(
            depth+1, predicates, allow_new_predicates)
        return f_AND(f1, f2), predicates, max(d1, d2)
    elif f == "NOT":
        f, predicates, _ = generate_formula(depth+1, predicates)
        return f_NOT(f), predicates
    elif f == "PREV":
        f, predicates, d = generate_formula(
            depth+1, predicates, allow_new_predicates)
        interval_bounds = generate_interval(True)
        return f_PREV(interval_bounds, f), predicates, d
    elif f == "NEXT":
        f, predicates, d = generate_formula(
            depth+1, predicates, allow_new_predicates)
        interval_bounds = generate_interval(False)
        return f_NEXT(interval_bounds, f), predicates, d
    elif f == "SINCE":
        f1, predicates, d1 = generate_formula(
            depth+1, predicates, allow_new_predicates)
        f2, predicates, d2 = generate_formula(
            depth+1, predicates, allow_new_predicates)
        interval_bounds = generate_interval(True)
        return f_SINCE(f1, interval_bounds, f2), predicates, max(d1, d2)
    elif f == "UNTIL":
        f1, predicates, d1 = generate_formula(
            depth+1, predicates, allow_new_predicates)
        f2, predicates, d2 = generate_formula(
            depth+1, predicates, allow_new_predicates)
        interval_bounds = generate_interval(False)
        return f_UNTIL(f1, interval_bounds, f2), predicates, max(d1, d2)
    else:
        print(f + " is not implemented (yet)")


def generate_formula(depth=0, predicates=[], allow_new_predicates=True):
    if depth < max_depth:
        f = formulas[random.randint(0, len(formulas)-1)]
        return generate_formula_aux(f, depth, predicates, allow_new_predicates)
    else:
        f = formulas[0]  # only allow terminal formulas
        return generate_formula_aux(f, depth, predicates, allow_new_predicates)


def maybe_generate_good_formula(depth=0, predicates=[], min_predicates=0, allow_new_predicates=True):
    f = generate_formula(depth, predicates, allow_new_predicates)
    x, preds, depth = f
    if len(preds) >= min_predicates and depth >= min_depth:
        return f
    else:
        return None


def generate_good_formula(depth=0, predicates=[], min_predicates=0, allow_new_predicates=True):
    while True:
        f = maybe_generate_good_formula(
            depth, predicates, min_predicates, allow_new_predicates)
        if not (f is None):
            return f


def write_file(f, text):
    with open(f, "w") as text_file:
        text_file.write(text)


p_f = os.path.join(output_dir, "formula.txt")
p_fr = os.path.join(output_dir, "formula-rewritten.txt")
p_fn = os.path.join(output_dir, "formula-native.txt")
p_sig = os.path.join(output_dir, "signature.txt")


def write_formula(f, p1, p2):
    x, preds, _ = f
    write_file(p1, x)
    write_file(p2, "\n".join(
        [pred + " (" + ",".join(["int" for var in vars]) + ")" for pred, vars in preds]))


def is_monitorable(p1, p2):
    check = os.popen(
        '../monpoly -formula ' + p1 + ' -sig ' + p2 + ' -no_rw -verified -check').read()

    if "The formula is monitorable." in check:
        return True
    else:
        return False


def maybe_generate_safe_formula(p1, p2, predicates=[], min_predicates=0, allow_new_predicates=True):
    f = generate_good_formula(
        0, predicates, min_predicates, allow_new_predicates)
    write_formula(f, p1, p2)

    monitorable = is_monitorable(p1, p2)

    os.remove(p1)
    os.remove(p2)

    if monitorable:
        return f
    else:
        return None


def generate_safe_formula(p1, p2, predicates=[], min_predicates=0, allow_new_predicates=True):
    while True:
        f = maybe_generate_safe_formula(
            p1, p2, predicates, min_predicates, allow_new_predicates)
        if not (f is None):
            return f


def maybe_generate_safe_trigger(type="0"):
    f2, predicates, d2 = generate_safe_formula(
        p_f, p_sig, [], min_predicates, True)
    # lhs doesn't have to be safe
    f1, predicates, d1 = generate_good_formula(
        0, predicates, min_predicates, False)

    if type == "0":
        bounded = (random.uniform(0, 1) >= 0.5)

        if bounded:
            upper_bound = str(generate_interval_bound())
            I = ["0", upper_bound]
        else:
            I = ["0", "*"]

        native_formula = f_TRIGGER(f1, I, f2)
        rewritten_formula = f_TRIGGER_SAFE_0(f1, I, f2)
    elif type == "unbounded":
        lower = generate_interval_bound(minimum=1)
        I = [str(lower), "*"]

        native_formula = f_AND(f_ONCE(I, f2), f_TRIGGER(f1, I, f2))
        rewritten_formula = f_TRIGGER_SAFE_UNBOUNDED(f1, I, f2)
    elif type == "bounded":
        lower = generate_interval_bound(minimum=1)
        upper = generate_interval_bound(minimum=lower)
        I = [str(lower), str(upper)]

        native_formula = f_AND(f_ONCE(I, f2), f_TRIGGER(f1, I, f2))
        rewritten_formula = f_TRIGGER_SAFE_BOUNDED(f1, I, f2)
    else:
        print(f'Unknown trigger type: {type}')
        exit(1)

    write_formula((rewritten_formula, predicates, 0), p_fr, p_sig)
    write_formula((native_formula, predicates, 0), p_fn, p_sig)

    if (is_monitorable(p_fn, p_sig)):
        return f1, f2, predicates
    else:
        return None


def generate_safe_trigger(type="0"):
    while True:
        f = maybe_generate_safe_trigger(type)
        if not (f is None):
            return f


f1, f2, predicates = generate_safe_trigger(type)

if (is_monitorable(p_fr, p_sig)):
    # print("The rewritten formula is monitorable!")
    pass
else:
    print("The rewritten formula isn't monitorable!")

if (is_monitorable(p_fn, p_sig)):
    # print("The native formula is monitorable!")
    pass
else:
    print("The native formula isn't monitorable!")
