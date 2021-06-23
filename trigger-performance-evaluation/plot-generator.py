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


args = parser.parse_args()

measurements = args.measurements
output = args.output
title = args.title

df = pd.read_csv(measurements, sep=";", quotechar='"', skipinitialspace=True)

# df.drop(['rewritten real time', 'native real time',
#         'rewritten sys time', 'native sys time'], axis=1)

df = df.sort_values(by=['experiment']).groupby('experiment').agg({
    'rewritten loop time': ['mean', 'std'],
    'native loop time': ['mean', 'std'],
    'native trigger time': ['mean', 'std']
})

labels = ["experiment " + str(i) for i in df.index.to_numpy()]
rewritten_means = df['rewritten loop time']['mean'].to_numpy()
native_means = df['native loop time']['mean'].to_numpy()
native_mmtaux_means = df['native trigger time']['mean'].to_numpy()

rewritten_stds = df['rewritten loop time']['std'].to_numpy()
native_stds = df['native loop time']['std'].to_numpy()
native_mmtaux_stds = df['native trigger time']['std'].to_numpy()

plt.rcParams["figure.figsize"] = (len(labels)+3, 5)

# the label locations
x = np.arange(len(labels))

# the width of the bars
width = 0.35

fig, ax = plt.subplots()
rects1 = ax.bar(x - width/2, rewritten_means, width,
                label='rewritten', yerr=rewritten_stds, ecolor='black', capsize=2)
rects2 = ax.bar(x + width/2, native_means, width,
                label='native', yerr=native_stds, ecolor='black', capsize=2)
# render them on top of rects2
rects3 = ax.bar(x + width/2, native_mmtaux_stds, width,
                label='mmtaux', yerr=native_mmtaux_stds, ecolor='black', capsize=2)

# Add some text for labels, title and custom x-axis tick labels, etc.
ax.set_ylabel('Running time in user mode in seconds')
ax.set_title(title)
ax.set_xticks(x)
ax.set_xticklabels(labels)
ax.legend()

# ax.bar_label(rects1, padding=3)
# ax.bar_label(rects2, padding=3)

fig.tight_layout()

plt.savefig(output, dpi=300)
