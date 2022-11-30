
(*
  SAVING AND LOADING STATE
*)

open Dllist
open Misc
open Predicate
open MFOTL
open Tuple
open Relation
open Sliding
open Helper
open Extformula
open Mformula

(*
  Converts the extformula to an mformula by recursing through the structure and reducing state information. The resulting
  formula thus has the same structure but minified state information.
  Main changes:
    - Once & Eventually have all pointers and trees removed

  neval dllist is converted to an array representation.
 *)
let ext_to_m ff =
  let el2m linf = linf.llast in
  let rec e2m = function
    | ERel           (rel, loc)                         -> MRel         (rel, loc)
    | EPred          (pred, c1, inf, loc)               -> MPred        (pred, c1, inf, loc)
    | ELet           (pred, c1, ext1, ext2, linf, loc)  -> MLet         (pred, c1, e2m ext1, e2m ext2, el2m linf, loc)
    | ENeg           (ext, loc)                         -> MNeg         (e2m ext, loc)
    | EAnd           (c2, ext1, ext2, ainf, loc)        -> MAnd         (c2, (e2m ext1), (e2m ext2), ainf, loc)
    | EOr            (c2, ext1, ext2, ainf, loc)        -> MOr          (c2, (e2m ext1), (e2m ext2), ainf, loc)
    | EExists        (c1, ext, loc)                     -> MExists      (c1, (e2m ext), loc)
    | EAggreg        (inf, comp, ext, loc)              -> MAggreg      (inf, comp, (e2m ext), loc)
    | EAggOnce       (inf, state, ext, loc)             -> MAggOnce     (inf, state, (e2m ext), loc)
    | EPrev          (intv, ext, pinf, loc)             -> MPrev        (intv, (e2m ext), pinf, loc)
    | ENext          (intv, ext, ninf, loc)             -> MNext        (intv, (e2m ext), ninf, loc)
    | ESince         (ext1, ext2, sinf, loc)            -> MSince       ((e2m ext1), (e2m ext2), sinf, loc)
    | EUntil         (ext1, ext2, uinf, loc)            -> MUntil       ((e2m ext1), (e2m ext2), uinf, loc)
  in e2m ff

(*
  Restores an mformula to its extformula representation by reconstructing the full state information,
  including optimization structures such as sliding trees.
*)
let m_to_ext mf =
  let ml2e mlast = {llast = mlast} in
  let rec m2e = function
    | MRel           (rel, loc)                        -> ERel         (rel, loc)
    | MPred          (pred, c1, inf, loc)              -> EPred        (pred, c1, inf, loc)
    | MLet           (pred, c1, mf1, mf2, mlast, loc)  -> ELet         (pred, c1, m2e mf1, m2e mf2, ml2e mlast, loc)
    | MNeg           (mf, loc)                         -> ENeg         ((m2e mf), loc)
    | MAnd           (c2, mf1, mf2, ainf, loc)         -> EAnd         (c2, (m2e mf1), (m2e mf2), ainf, loc)
    | MOr            (c2, mf1, mf2, ainf, loc)         -> EOr          (c2, (m2e mf1), (m2e mf2), ainf, loc)
    | MExists        (c1, mf, loc)                     -> EExists      (c1, (m2e mf), loc)
    | MAggreg        (inf, comp, mf, loc)              -> EAggreg      (inf, comp, (m2e mf), loc)
    | MAggOnce       (inf, state, mf, loc)             -> EAggOnce     (inf, state, (m2e mf), loc)
    | MPrev          (intv, mf, pinf, loc)             -> EPrev        (intv, (m2e mf), pinf, loc)
    | MNext          (intv, mf, ninf, loc)             -> ENext        (intv, (m2e mf), ninf, loc)
    | MSince         (mf1, mf2, sinf, loc)             -> ESince       ((m2e mf1), (m2e mf2), sinf, loc)
    | MUntil         (mf1, mf2, uinf, loc)             -> EUntil       ((m2e mf1), (m2e mf2), uinf, loc)
  in m2e mf

(* END SAVING AND LOADING STATE *)
