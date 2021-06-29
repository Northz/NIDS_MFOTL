import argparse
import random
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

parser = argparse.ArgumentParser()
parser.add_argument('--measurements',
                    help='The measurement csv', required=True)
parser.add_argument('--output',
                    help='The output path and filename', required=True)
parser.add_argument('--title', help='The plot title')
parser.add_argument(
    '--yscale', help='The scale of the y-axis. Default: linear')


args = parser.parse_args()

measurements = args.measurements
output = args.output
title = args.title
yscale = args.yscale

df = pd.read_csv(measurements, sep=";", quotechar='"', skipinitialspace=True)

# df.drop(['rewritten real time', 'native real time',
#         'rewritten sys time', 'native sys time'], axis=1)

df = df.sort_values(by=['experiment']).groupby('experiment').agg({
    'rewritten real time': ['mean', 'std'],
    'rewritten meval time': ['mean', 'std'],
    'native real time': ['mean', 'std'],
    'native meval time': ['mean', 'std'],
    'native trigger time': ['mean', 'std']
})

labels = ["experiment " + str(i) for i in df.index.to_numpy()]
#rewritten_means = df['rewritten real time']['mean'].to_numpy()
rewritten_meval_means = df['rewritten meval time']['mean'].to_numpy()
#native_means = df['native real time']['mean'].to_numpy()
native_meval_means = df['native meval time']['mean'].to_numpy()
native_mmtaux_means = df['native trigger time']['mean'].to_numpy()

#rewritten_stds = df['rewritten real time']['std'].to_numpy()
rewritten_meval_stds = df['rewritten meval time']['std'].to_numpy()
#native_stds = df['native real time']['std'].to_numpy()
native_meval_stds = df['native meval time']['std'].to_numpy()
native_mmtaux_stds = df['native trigger time']['std'].to_numpy()

plt.rcParams["figure.figsize"] = (len(labels)+3, 5)

# the label locations
x = np.arange(len(labels))

# the width of the bars
width = 0.35

fig, ax = plt.subplots()
# rects_rewritten = ax.bar(x - width/2, rewritten_means, width,
#                          label='rewritten', yerr=rewritten_stds, ecolor='black', capsize=2, color='#3498db')
rects_rewritten_meval = ax.bar(x - width/2, rewritten_meval_means, width,
                               label='rewritten meval', yerr=rewritten_meval_stds, ecolor='black', capsize=2)  # , color='#2980b9'

# rects_native = ax.bar(x + width/2, native_means, width,
#                       label='native', yerr=native_stds, ecolor='black', capsize=2, color='#e67e22')
rects_native_meval = ax.bar(x + width/2, native_meval_means, width,
                            label='native meval', yerr=native_meval_stds, ecolor='black', capsize=2)  # , color='#d35400'
rects_native_mmtaux = ax.bar(x + width/2, native_mmtaux_means, 0.75*width,
                             label='mmtaux', yerr=native_mmtaux_stds, ecolor='black', capsize=2)  # , color='#2ecc71'

# Add some text for labels, title and custom x-axis tick labels, etc.
ax.set_ylabel('Running time of meval in seconds')
ax.set_title(title)
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.legend()

if yscale == "log":
    plt.yscale('log')

# ax.bar_label(rects1, padding=3)
# ax.bar_label(rects2, padding=3)

fig.tight_layout()

plt.savefig(output, dpi=300)
