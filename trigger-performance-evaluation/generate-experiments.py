import os


def gen_int(interval, length):
    interval = interval.replace('a', str(int(0.25 * length)))
    interval = interval.replace('b', str(int(0.75 * length)))
    return interval


def write_file(f, text):
    with open(f, "w") as text_file:
        text_file.write(text)


rhs = "B(x,y)"


def lhs_to_s(lhs):
    if lhs == "FALSE":
        return "lhs-0"
    elif lhs == "A(x)":
        return "lhs-1"
    elif lhs == "A(x,y)":
        return "lhs-2"
    else:
        raise ValueError(f'Unknown lhs: {lhs}')


def int_to_s(interval):
    if interval == "[0,*]":
        return "0-unbounded"
    elif interval == "[0,b]":
        return "0-bounded"
    elif interval == "[a,*]":
        return "a-unbounded"
    elif interval == "[a,b]":
        return "a-bounded"
    else:
        raise ValueError(f'Unknown interval: {interval}')


# trigger
for interval in ["[0,*]", "[0,b]", "[a,*]", "[a,b]"]:
    for lhs in ["FALSE", "A(x)", "A(x,y)"]:
        for log_type in ["historically", "since", "once"]:
            for asymptotic in ["baseline", "2n", "2l"]:
                # once is only allowed for a > 0
                if log_type == "once" and (interval != "[a,*]" and interval != "[a,b]"):
                    continue

                # if 0 is not in the interval, the lhs has to be A(x, y) (same set of free variables)
                if (interval == "[a,*]" or interval == "[a,b]") and (lhs != "A(x,y)"):
                    continue

                # intervals of the form [a,b] are much slower!
                if interval == "[a,b]":
                    length = 10 ** 2
                elif interval == "[a,*]":
                    length = 2 * 10 ** 2
                else:
                    length = 10 ** 3

                n = 10 ** 2

                if asymptotic == "baseline":
                    pass
                elif asymptotic == "2n":
                    n = 2 * n
                elif asymptotic == "2l":
                    length = 2 * length

                experiment = f'trigger-{int_to_s(interval)}-{lhs_to_s(lhs)}-{log_type}'
                print(f'Generating experiment {experiment}..')

                output = os.path.join(
                    "./experiments", experiment)
                if not(os.path.isdir(output)):
                    os.makedirs(output)

                formula_path = os.path.join(
                    output, f'formula-{asymptotic}.txt')
                signature_path = os.path.join(output, "signature.txt")
                log_path = os.path.join(output, f'log-{asymptotic}.txt')

                # if 0 is not in the interval, we have to use a conjunction
                if (interval == "[a,*]" or interval == "[a,b]"):
                    write_file(formula_path,
                               f'({rhs}) AND (({lhs}) TRIGGER{gen_int(interval, length)} ({rhs}))')
                else:
                    write_file(formula_path,
                               f'({lhs}) TRIGGER{gen_int(interval, length)} ({rhs})')

                if lhs == "A(x)":
                    write_file(signature_path,
                               f'A (int)\nB(int,int)')
                elif lhs == "A(x,y)":
                    write_file(signature_path,
                               f'A (int,int)\nB(int,int)')
                else:
                    write_file(signature_path,
                               f'B(int,int)')

                # to generate the log, execute the other script
                os.system(
                    f'python ./log-generator.py --formula {formula_path} --pattern {log_type} --output {log_path} --length {length} --n {n}')
                # print(
                #    f'Check execution time of experiment {experiment} ({asymptotic})..')
                #os.system(f'./measure-single.sh {experiment} {asymptotic}')
