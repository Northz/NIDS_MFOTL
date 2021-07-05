import argparse
import random
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

asymptotic_order = ["16l", "8l", "4l", "2l",
                    "baseline", "2n", "4n", "8n", "16n"]


def index_to_key(idx):
    if "trigger" in idx[0]:
        # don't apply the function on the first level
        return idx

    return idx.map(asymptotic_order.index)


parser = argparse.ArgumentParser()
parser.add_argument('--measurements',
                    help='The measurement csv', required=True)
parser.add_argument('--output',
                    help='The output directory', required=True)
#parser.add_argument( '--yscale', help='The scale of the y-axis. Default: linear')


args = parser.parse_args()

measurements = args.measurements
output = args.output
#yscale = args.yscale

df = pd.read_csv(measurements, sep=";", quotechar='"', skipinitialspace=True)

# df.drop(['rewritten real time', 'native real time',
#         'rewritten sys time', 'native sys time'], axis=1)

experiments = pd.unique(df.sort_values(by=['experiment']).experiment)
asymptotics = pd.unique(df.sort_values(by=['asymptotic']).asymptotic)

df = df.groupby(['experiment', 'asymptotic']).agg({
    'native real time': ['mean', 'std'],
    'native meval time': ['mean', 'std'],
    'native trigger time': ['mean', 'std']
})

for experiment_name in experiments:
    exp = df.loc[[(experiment_name, a) for a in asymptotics]]
    exp = exp.sort_index(ascending=[True, False],
                         sort_remaining=False, key=index_to_key)

    labels = []
    for e, a in exp.index:
        labels.append(a)

    #native_means = df['native real time']['mean'].to_numpy()
    native_meval_means = exp['native meval time']['mean'].to_numpy()
    native_mmtaux_means = exp['native trigger time']['mean'].to_numpy()

    #native_stds = df['native real time']['std'].to_numpy()
    native_meval_stds = exp['native meval time']['std'].to_numpy()
    native_mmtaux_stds = exp['native trigger time']['std'].to_numpy()

    #plt.rcParams["figure.figsize"] = (len(labels)+3, 5)

    # the label locations
    x = np.arange(len(labels))

    # the width of the bars
    width = 0.35

    fig, ax = plt.subplots()
    # rects_native = ax.bar(x + width/2, native_means, width,
    #                       label='native', yerr=native_stds, ecolor='black', capsize=2, color='#e67e22')
    rects_native_meval = ax.bar(x, native_meval_means, width,
                                label='native meval', yerr=native_meval_stds, ecolor='black', capsize=2)  # , color='#d35400'
    rects_native_mmtaux = ax.bar(x, native_mmtaux_means, 0.75*width,
                                 label='mmtaux', yerr=native_mmtaux_stds, ecolor='black', capsize=2)  # , color='#2ecc71'

    # Add some text for labels, title and custom x-axis tick labels, etc.
    ax.set_ylabel('Running time of meval in seconds')
    ax.set_xticks(x)
    ax.set_xticklabels(labels)
    ax.legend()

    # plt.yscale('log')
    # if "a-bounded" in experiment_name:
    #     plt.yscale('log')
    # else:
    #     plt.yscale('linear')

    # ax.bar_label(rects1, padding=3)
    # ax.bar_label(rects2, padding=3)

    fig.tight_layout()

    plt.savefig(os.path.join(output, f'{experiment_name}.png'), dpi=300)
