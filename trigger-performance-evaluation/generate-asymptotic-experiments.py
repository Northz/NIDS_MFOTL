import os


def gen_int(interval, length, interval_size):
    if interval == "[a,b]":
        interval = interval.replace(
            'a', str(int((1 - interval_size)/2 * length)))
        interval = interval.replace(
            'b', str(int((1 - (1 - interval_size)/2) * length)))
    elif interval == "[a,*]":
        interval = interval.replace(
            'a', str(int((1-interval_size) * length)))
    elif interval == "[0,b]":
        interval = interval.replace(
            'b', str(int(interval_size * length)))

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
for interval in ["[a,b]"]:
    for lhs in ["A(x,y)"]:
        for log_type in ["historically", "since", "once"]:
            for asymptotic in ["baseline", "2n", "2l", "4n", "4l", "8n", "8l", "16n", "16l"]:
                # once is only allowed for a > 0
                if log_type == "once" and (interval != "[a,*]" and interval != "[a,b]"):
                    continue

                # if 0 is not in the interval, the lhs has to be A(x, y) (same set of free variables)
                if (interval == "[a,*]" or interval == "[a,b]") and (lhs != "A(x,y)"):
                    continue

                if interval == "[0,*]" and asymptotic == "2i":
                    continue

                #orig_length = 10 ** 2

                length = 10 ** 2
                n = 10 ** 2
                interval_size = 0.75

                if asymptotic == "baseline":
                    pass
                elif asymptotic == "2n":
                    n = 2 * n
                elif asymptotic == "2l":
                    length = 2 * length
                elif asymptotic == "4n":
                    n = 4 * n
                elif asymptotic == "4l":
                    length = 4 * length
                elif asymptotic == "8n":
                    n = 8 * n
                elif asymptotic == "8l":
                    length = 8 * length
                elif asymptotic == "16n":
                    n = 16 * n
                elif asymptotic == "16l":
                    length = 16 * length

                experiment = f'trigger-{int_to_s(interval)}-{lhs_to_s(lhs)}-{log_type}'
                print(f'Generating experiment {experiment} ({asymptotic})..')

                output = os.path.join(
                    "./asymptotic-experiments", experiment)
                if not(os.path.isdir(output)):
                    os.makedirs(output)

                formula_path = os.path.join(
                    output, f'formula-{asymptotic}.txt')
                signature_path = os.path.join(output, "signature.txt")
                log_path = os.path.join(output, f'log-{asymptotic}.txt')

                # if 0 is not in the interval, we have to use a conjunction
                if (interval == "[a,*]" or interval == "[a,b]"):
                    write_file(formula_path,
                               f'({rhs}) AND (({lhs}) TRIGGER{gen_int(interval, length, interval_size)} ({rhs}))')
                else:
                    write_file(formula_path,
                               f'({lhs}) TRIGGER{gen_int(interval, length, interval_size)} ({rhs})')

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
