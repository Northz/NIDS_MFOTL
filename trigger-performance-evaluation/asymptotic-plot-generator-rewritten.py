import argparse
import random
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

asymptotic_order = ["16l", "8l", "4l", "2l",
                    "baseline", "2n", "4n", "8n", "16n"]


def index_to_key(idx):
    if "trigger" in idx[0] or "release" in idx[0]:
        # don't apply the function on the first level
        return idx

    return idx.map(asymptotic_order.index)


parser = argparse.ArgumentParser()
parser.add_argument('--measurements',
                    help='The measurement csv', required=True)
parser.add_argument('--output',
                    help='The output directory', required=True)
# parser.add_argument( '--yscale', help='The scale of the y-axis. Default: linear')


args = parser.parse_args()

measurements = args.measurements
output = args.output
# yscale = args.yscale

df = pd.read_csv(measurements, sep=";", quotechar='"', skipinitialspace=True)

# df.drop(['rewritten real time', 'native real time',
#         'rewritten sys time', 'native sys time'], axis=1)

experiments = pd.unique(df.sort_values(by=['experiment']).experiment)
asymptotics = pd.unique(df.sort_values(by=['asymptotic']).asymptotic)

df = df.groupby(['experiment', 'asymptotic']).agg({
    'rewritten meval time': ['mean', 'std']
})

plt.rcParams.update({
    "text.usetex": True
})

for experiment_name in experiments:
    exp = df.loc[[(experiment_name, a) for a in asymptotics]]
    exp = exp.sort_index(ascending=[True, False],
                         sort_remaining=False, key=index_to_key)

    labels = [a for e, a in exp.index]
    baselineIndex = labels.index("baseline")
    nExps = baselineIndex + 1
    lExps = len(labels) - baselineIndex

    x_n = (list(range(nExps)))
    x_n.reverse()
    x_n = np.array(x_n)

    x_l = np.array(list(range(lExps)))

    # native_means = df['native real time']['mean'].to_numpy()
    rewritten_meval_means = exp['rewritten meval time']['mean'].to_numpy()

    # native_stds = df['native real time']['std'].to_numpy()
    rewritten_meval_stds = exp['rewritten meval time']['std'].to_numpy()

    A_n = np.vstack([x_n, np.ones(3)]).T
    a_n, b_n = np.linalg.lstsq(
        A_n, rewritten_meval_means[0:baselineIndex+1], rcond=None)[0]

    A_l = np.vstack([x_l, np.ones(3)]).T
    a_l, b_l = np.linalg.lstsq(
        A_l, rewritten_meval_means[baselineIndex:], rcond=None)[0]

    linearFunctionX_n = np.linspace(0, 2, 100)
    linearFunctionY_n = a_n * (2 - linearFunctionX_n) + \
        b_n  # start at x = 2, -a * x + b

    linearFunctionX_l = np.linspace(2, 4, 100)
    linearFunctionY_l = a_l * (linearFunctionX_l-2) + \
        b_l  # start at x = 2, a * x + b

    plt.rcParams["figure.figsize"] = (5, 5)

    # the label locations
    x = np.arange(len(labels))

    # the width of the bars
    width = 0.35

    fig, ax = plt.subplots()
    # rects_native = ax.bar(x + width/2, native_means, width,
    #                       label='native', yerr=native_stds, ecolor='black', capsize=2, color='#e67e22')
    rects_native_meval = ax.bar(x, rewritten_meval_means, width,
                                label='meval', yerr=rewritten_meval_stds, ecolor='black', capsize=2, color='tab:purple')  # , color='#d35400'

    plt.ylim(bottom=0)
    plt.plot(linearFunctionX_n, linearFunctionY_n, 'black', linestyle='dotted')
    plt.plot(linearFunctionX_l, linearFunctionY_l, 'black', linestyle='dashed')

    # custom legend
    custom_lines = [Line2D([0], [0], color="black", lw=1, linestyle='dotted'),
                    Line2D([0], [0], color="black", lw=1, linestyle='dashed')]
    legend = [str(round(a_n, 2)) + r'$ \: \cdot \: x \: + \: $' + str(round(b_n, 2)),
              str(round(a_l, 2)) + r'$\: \cdot \: x \: + \:$' + str(round(b_l, 2))]

    if "a-" in experiment_name:
        B_l = np.vstack([x_l*x_l, x_l, np.ones(3)]).T
        a_l, b_l, c_l = np.linalg.lstsq(
            B_l, rewritten_meval_means[baselineIndex:], rcond=None)[0]

        quadraticFunctionX_l = np.linspace(2, 4, 100)
        quadraticFunctionY_l = a_l * ((quadraticFunctionX_l-2) ** 2) + b_l * (quadraticFunctionX_l-2) + \
            c_l  # start at x = 2, a * x^2 + b * x + c

        plt.plot(quadraticFunctionX_l, quadraticFunctionY_l,
                 'silver', linestyle='dashdot')
        custom_lines.append(
            Line2D([0], [0], color="silver", lw=1, linestyle='dashdot'))
        legend.append(str(round(a_l, 2)) +
                      r'$\: \cdot \: x^2 \: + \:$' + str(round(b_l, 2)) + r'$\: \cdot \: x \: + \:$' + str(round(c_l, 2)))

    ax.legend(custom_lines, legend)

    # Add some text for labels, title and custom x-axis tick labels, etc.
    # ax.set_ylabel('Running time in seconds')
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    # ax.legend()

    # plt.yscale('log')
    # if "a-bounded" in experiment_name:
    #     plt.yscale('log')
    # else:
    #     plt.yscale('linear')

    # ax.bar_label(rects1, padding=3)
    # ax.bar_label(rects2, padding=3)

    fig.tight_layout()

    plt.savefig(os.path.join(output, f'{experiment_name}.png'), dpi=300)
