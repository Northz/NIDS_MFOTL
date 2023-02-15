# Before pushing changes to master involving the formal theories

## 1. Update dependency graph
If the dependency graph changed, update pairs below. You can see the graph by copying and pasting the pairs as input to your favorite visualizer e.g. [WebGraphviz](http://www.webgraphviz.com/) or [ascii-graphs](https://github.com/mdr/ascii-graphs):

    "Preliminaries" -> "Formula"
    "Regex" -> "Formula"
    "MFOTL" -> "Formula"
    "Containers" -> "Formula"
    "Formula" -> "Safety"
    "Formula" -> "Rewriting"
    "Safety" -> "Progress"
    "Safety" -> "Typing"
    "Safety" -> "Slicing"
    "Progress" -> "Safety_Proofs"
    "Typing" -> "Type_Soundness"
    "Typing" -> "Monitor"
    "Optimized_Join" -> "Monitor"
    "Monitor" -> "Correct_Un_Ops"
    "Progress" -> "Correct_Un_Ops"
    "Monitor" -> "Correct_Regex"
    "Progress" -> "Correct_Regex"
    "Monitor" -> "Correct_Agg"
    "Progress" -> "Correct_Agg"
    "Monitor" -> "Correct_Bin_Ops"
    "Progress" -> "Correct_Bin_Ops"
    "Correct_Agg" -> "Correct_Since"
    "Correct_Agg" -> "Correct_Until"
    "Correct_Until" -> "Correct_Trigger"
    "Correct_Bin_Ops" -> "Correct_Until"
    "Correct_Un_Ops" -> "Correctness"
    "Correct_Regex" -> "Correctness"
    "Correct_Since" -> "Correctness"
    "Correct_Trigger" -> "Correctness"
    "Correctness" -> "Sat"
    "Monitor" -> "Optimized_Common"
    "Monitor" -> "Optimized_Agg"
    "Optimized_Common" -> "Optimized_Since"
    "Optimized_Common" -> "Optimized_Trigger"
    "Optimized_Common" -> "Optimized_Until"
    "Optimized_Agg" -> "Optimized_Agg_Temporal"
    "Optimized_Since" -> "Optimized_Agg_Temporal"
    "Optimized_Until" -> "Optimized_Agg_Temporal"
    "Optimized_Trigger" -> "Monitor_Impl"
    "Optimized_Agg_Temporal" -> "Monitor_Impl"
    "Monitor_Impl" -> "Monitor_Code"

## 2. Update ROOT file
Add any new theories to the `ROOT` file. All theory-files should appear in the `ROOT` file in the order of the dependency graph.

## 3. Build the Isabelle sessions
Check that all Isabelle sessions can be built without error with the latest Isabelle version:

    isabelle build -D path_to_dir_where_MFODL_Monitor_Devel_ROOT_file_is

## 4. Export `verified.ml`
Export the code-generated file `verified.ml` and copy it to the `src` directory.

## 5. Run `dune test`
Run `dune test` from the repository root. If the new `verified.ml` is different from the previous version, you should also check whether each change in the generated code is actually expected.



