(*
**
** An implementation of functional maps based on AVL trees.
**
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: August, 2009
**
*)

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

(* ****** ****** *)

(*
** An implementation of doubly-linked AVL trees
*)

%{^
#include "atspre.h"
%}

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0 // no dynamic loading

(* ****** ****** *)

sortdef t0p = t@ype and vt0p = viewt@ype
sortdef anz = {a:addr | a <> null}

(* ****** ****** *)

absviewtype map_vt (key:t@ype,itm:viewt@ype+)

(* ****** ****** *)

typedef cmp (key:t@ype) = (key, key) -<cloref> Sgn

extern fun{key:t0p}
  compare_key_key (x1: key, x2: key, cmp: cmp key):<> Sgn
// end of [compare_key_key]

implement{key} compare_key_key (x1, x2, cmp) = cmp (x1, x2)

(* ****** ****** *)

extern fun{}
linmap_empty {key:t0p;itm:vt0p} ():<> map_vt (key, itm)

extern fun{}
linmap_empty_free {key:t0p;itm:vt0p}
  (m: !map_vt (key, itm) >> opt (map_vt (key, itm), tag)): #[tag:bool] bool tag
// end of [linmap_empty_free]

(* ****** ****** *)

extern fun{}
linmap_is_empty {key:t0p;itm:vt0p} (m: !map_vt (key, itm)):<> bool

extern fun{}
linmap_isnot_empty {key:t0p;itm:vt0p} (m: !map_vt (key, itm)):<> bool

(* ****** ****** *)

// this is O(1)-time
extern fun{key:t0p;itm:vt0p} linmap_height (m: !map_vt (key, itm)):<> Nat

// this is O(n)-time
extern fun{key:t0p;itm:vt0p} linmap_size (m: !map_vt (key, itm)):<> Nat

(* ****** ****** *)

viewtypedef avlnode (
  key:t@ype, itm:viewt@ype, height:int, left:addr, right:addr, parent:addr
) = @{
  key= key, itm= itm
, height= int height
, left= ptr left, right= ptr right
, parent= ptr parent
} // end of [avlnode]

viewtypedef avlnode (
  key:t@ype, itm:viewt@ype
) = @{
  key= key, itm= itm
, height= int?
, left= ptr?, right= ptr?
, parent= ptr?
} // end of [avlnode]

typedef
avlnode0 (key:t@ype,itm:viewt@ype) = avlnode (key, itm)?
// end of [avlnode0]

dataview
avltree_v (
  key : t@ype
, itm : viewt@ype+
, int  // height
, addr // parent
, addr // self
) = (* view for doubly-linked AVL trees *)
  | {h,hl,hr:nat |
     hl <= hr+1; hr <= hl+1; h==max(hl,hr)+1}
    {lft,rgh,pnt:addr} {slf:addr | slf <> null}
    B (key, itm, h, pnt, slf) of (
      avlnode (key, itm, h, lft, rgh, pnt) @ slf
    , avltree_v (key, itm, hl, slf, lft), avltree_v (key, itm, hr, slf, rgh)
    ) // end of [B]
  | {pnt:addr} E (key, itm, 0, pnt, null) of ()
// end of [dataview avltree_v]

(* ****** ****** *)

fn{key:t0p;itm:vt0p}
  avltree_height_get {h:nat} {pnt:addr} {slf:addr}
  (pf: !avltree_v (key, itm, h, pnt, slf) | p: ptr slf):<> int h =
  if p <> null then let
    prval B (pf_at, pf_l, pf_r) = pf
    val h = p->height
    prval () = pf := B (pf_at, pf_l, pf_r)
  in
    h
  end else let
    prval E () = pf; prval () = pf := E {key,itm} {pnt} ()
  in
    0
  end // end of [if]
// end of [avltree_height_get]

(* ****** ****** *)

fn{key:t0p;itm:vt0p} avltree_parent_set
  {h:nat} {pnt0:addr} {slf:addr} {pnt1:addr} (
    pf: !avltree_v (key, itm, h, pnt0, slf) >> avltree_v (key, itm, h, pnt1, slf)
  | p: ptr slf, pp1: ptr pnt1
  ) :<> void =
  if p <> null then let
    prval B (pf_at, pf_l, pf_r) = pf
    val () = p->parent := pp1
    prval () = pf := B (pf_at, pf_l, pf_r)
  in
    // nothing
  end else let
    prval E () = pf; prval () = pf := E {key,itm} {pnt1} ()
  in
    // nothing
  end // end of [if]
// end of [avltree_parent_set]

(* ****** ****** *)

(*
** left rotation for restoring height invariant
*)
fn{key:t0p;itm:vt0p} avltree_lrotate
  {h:int} {hl,hr:nat | hl+2 == hr} {slf:anz;lft,rgh,pnt:addr} (
    pf_at: avlnode (key, itm, h, lft, rgh, pnt) @ slf
  , pf_l: avltree_v (key, itm, hl, slf, lft), pf_r: avltree_v (key, itm, hr, slf, rgh)
  | p: ptr slf
  ) :<> [h:int | hr <= h; h <= hr+1] [slf:anz] (avltree_v (key, itm, h, pnt, slf) | ptr slf)
  = let
  val pp = p->parent
  val p_l = p->left and p_r = p->right
  prval B (pf_r_at, pf_r_l, pf_r_r) = pf_r
  val p_r_l = p_r->left and p_r_r = p_r->right
  val hrl = avltree_height_get (pf_r_l | p_r_l)
  val hrr = avltree_height_get (pf_r_r | p_r_r)
in
  if hrl <= hrr then let
    val () = p_r->height := hrl+2
    val () = p_r->parent := pp
    val () = p_r->left := p
    val () = p->height := hrl+1
    val () = p->parent := p_r
    val () = p->right := p_r_l
    val () = avltree_parent_set<key,itm> (pf_r_l | p_r_l, p)
    prval pf_l = B {key,itm} (pf_at, pf_l, pf_r_l) and pf_r = pf_r_r
  in
    (B {key,itm} (pf_r_at, pf_l, pf_r) | p_r)
  end else let // [hrl > hrr]: deep rotation
    val hr = p_r->height
    prval B (pf_r_l_at, pf_r_l_l, pf_r_l_r) = pf_r_l
    val p_r_l_l = p_r_l->left and p_r_l_r = p_r_l->right
    val () = p_r_l->height := hr
    val () = p_r_l->parent := pp
    val () = p_r_l->left := p
    val () = p_r_l->right := p_r
    val () = p->height := hrl
    val () = p->parent := p_r_l
    val () = p->right := p_r_l_l
    val () = p_r->height := hrl
    val () = p_r->parent := p_r_l
    val () = p_r->left := p_r_l_r
    val () = avltree_parent_set<key,itm> (pf_r_l_l | p_r_l_l, p)
    prval pf_l = B {key,itm} (pf_at, pf_l, pf_r_l_l)
    val () = avltree_parent_set<key,itm> (pf_r_l_r | p_r_l_r, p_r)
    prval pf_r = B {key,itm} (pf_r_at, pf_r_l_r, pf_r_r)
  in
    (B {key,itm} (pf_r_l_at, pf_l, pf_r) | p_r_l)
  end (* end of [if] *)
end // end of [avltree_lrotate]

(* ****** ****** *)

(*
** right rotation for restoring height invariant
*)
fn{key:t0p;itm:vt0p} avltree_rrotate
  {h:int} {hl,hr:nat | hl == hr+2} {slf:anz;lft,rgh,pnt:addr} (
    pf_at: avlnode (key, itm, h, lft, rgh, pnt) @ slf
  , pf_l: avltree_v (key, itm, hl, slf, lft), pf_r: avltree_v (key, itm, hr, slf, rgh)
  | p: ptr slf
  ) :<> [h:int | hl <= h; h <= hl+1] [slf:anz] (avltree_v (key, itm, h, pnt, slf) | ptr slf)
  = let
  val pp = p->parent
  val p_l = p->left and p_r = p->right
  prval B (pf_l_at, pf_l_l, pf_l_r) = pf_l
  val p_l_l = p_l->left and p_l_r = p_l->right
  val hll = avltree_height_get (pf_l_l | p_l_l)
  val hlr = avltree_height_get (pf_l_r | p_l_r)
in
  if hll >= hlr then let
    val () = p_l->height := hlr+2
    val () = p_l->parent := pp
    val () = p_l->right := p
    val () = p->height := hlr+1
    val () = p->parent := p_l
    val () = p->left := p_l_r
    val () = avltree_parent_set<key,itm> (pf_l_r | p_l_r, p)
    prval pf_l = pf_l_l and pf_r = B {key,itm} (pf_at, pf_l_r, pf_r)
  in
    (B {key,itm} (pf_l_at, pf_l, pf_r) | p_l)
  end else let // [hll < hlr]: deep rotation
    val hl = p_l->height
    prval B (pf_l_r_at, pf_l_r_l, pf_l_r_r) = pf_l_r
    val p_l_r_l = p_l_r->left and p_l_r_r = p_l_r->right
    val () = p_l_r->height := hl
    val () = p_l_r->parent := pp
    val () = p_l_r->left := p_l
    val () = p_l_r->right := p
    val () = p_l->height := hlr
    val () = p_l->parent := p_l_r
    val () = p_l->right := p_l_r_l
    val () = p->height := hlr
    val () = p->parent := p_l_r
    val () = p->left := p_l_r_r
    val () = avltree_parent_set<key,itm> (pf_l_r_l | p_l_r_l, p_l)
    prval pf_l = B {key,itm} (pf_l_at, pf_l_l, pf_l_r_l)
    val () = avltree_parent_set<key,itm> (pf_l_r_r | p_l_r_r, p)
    prval pf_r = B {key,itm} (pf_at, pf_l_r_r, pf_r)
  in
    (B {key,itm} (pf_l_r_at, pf_l, pf_r) | p_l_r)
  end (* end of [if] *)
end // end of [avltree_rrotate]

(* ****** ****** *)

dataview avldiff_v (
  key : t@ype
, itm : viewt@ype+
, int  // height: for termination metrics
, int  // the height of the missing avltree
, addr // child: the root of the missing avltree
, int  // direction: left(0) or right(1)
, addr // root
, addr // root parent
, addr // self
) = (* view for an avltree minus a sub avltree *)
  | {n,h:nat | h <= n}
    {hl,hr:nat | hl <= hr+1; hr <= hl+1; h==max(hl,hr)+1}
    {lft,rgh,pnt:addr} {dir:two} {rt,rtp:addr}
    {slf:addr | slf <> null}
    B1L (key, itm, n, hl, lft, 0, rt, rtp, slf) of (
      avlnode (key, itm, h, lft, rgh, pnt) @ slf
    , avldiff_v (key, itm, n, h, slf, dir, rt, rtp, pnt), avltree_v (key, itm, hr, slf, rgh)
    ) // end of [B1L]
  | {n,h:nat | h <= n}
    {hl,hr:nat | hl <= hr+1; hr <= hl+1; h==max(hl,hr)+1}
    {lft,rgh,pnt:addr} {dir:two} {rt,rtp:addr}
    {slf:addr | slf <> null}
    B1R (key, itm, n, hr, rgh, 1, rt, rtp, slf) of (
      avlnode (key, itm, h, lft, rgh, pnt) @ slf
    , avltree_v (key, itm, hl, slf, lft), avldiff_v (key, itm, n, h, slf, dir, rt, rtp, pnt)
    ) // end of [B1R]
  | {h:nat} {chld:addr} {dir:two} {slf:addr}
    E1 (key, itm, h, h, chld, dir, chld, slf, slf) of ()
// end of [avldiff_v]

(* ****** ****** *)

prfun avldiff_avltree_join {key:t0p;itm:vt0p}
  {n,h:nat | h <= n} {chld:addr} {dir:two} {rt,rtp:addr}
  {slf:addr} .<n-h>. (
    fpf: avldiff_v (key, itm, n, h, chld, dir, rt, rtp, slf)
  , pf0: avltree_v (key, itm, h, slf, chld) // view for the missing avltree
  ) :<prf> avltree_v (key, itm, n, rtp, rt) =
  case+ fpf of
  | B1L (pf_at, fpf_l, pf_r) => avldiff_avltree_join (fpf_l, B (pf_at, pf0, pf_r))
  | B1R (pf_at, pf_l, fpf_r) => avldiff_avltree_join (fpf_r, B (pf_at, pf_l, pf0))
  | E1 () => pf0
// end of [avldiff_avltree_join]

(* ****** ****** *)

prfun avldiff_takeout {key:t0p;itm:vt0p}
  {n,h:int} {chld:addr} {dir:int} {rt,rtp:addr}
  {slf:addr | slf <> rtp} .<>. (
    fpf: avldiff_v (key, itm, n, h, chld, dir, rt, rtp, slf)
  ) :<prf> [h0:int;lft,rgh,pnt:addr] (
    avlnode (key, itm, h0, lft, rgh, pnt) @ slf
  , avlnode (key, itm, h0, lft, rgh, pnt) @ slf
      -<lin> avldiff_v (key, itm, n, h, chld, dir, rt, rtp, slf)
  ) = case+ fpf of
  | B1L {..} {_,h0} {..} {lft,rgh,pnt} {..} {rt,rtp} (pf_at, fpf_l, pf_r) =>
      #[h0,lft,rgh,pnt | (pf_at, llam (pf_at) => B1L (pf_at, fpf_l, pf_r))]
    // end of [B1L]
  | B1R {..} {_,h0} {..} {lft,rgh,pnt} {..} {rt,rtp} (pf_at, pf_l, fpf_r) =>
      #[h0,lft,rgh,pnt | (pf_at, llam (pf_at) => B1R (pf_at, pf_l, fpf_r))]
    // end of [B1R]
// end of [avldiff_takeout]

(* ****** ****** *)

fn{key:t0p;itm:vt0p} avldiff_dir_get
  {n,h:int} {chld:addr | chld <> null} {dir:int} {rt:addr}
  {slf:addr} (
    fpf: !avldiff_v (key, itm, n, h, chld, dir, rt, null, slf) | p: ptr slf, pc: ptr chld
  ) :<> int dir = let
  val dir = if p <> null then let
    prval (pf_at, ffpf) = avldiff_takeout (fpf)
    val dir = (if pc = p->left then 0(*left*) else 1(*right*)): int
    prval () = fpf := ffpf (pf_at)
  in
    dir
  end else begin
    0 // it is arbitrarily chosen (from {0,1})
  end : int
in
  __cast (dir) where { extern castfn __cast (_: int):<> int dir }
end // end of [avldiff_dir_get]

(* ****** ****** *)

fn{key:t0p;itm:vt0p} avldiff_child_set
  {n,h:int} {chld:addr} {dir:int} {rt,rtp:addr}
  {slf:addr | slf <> rtp} {chld1:addr} (
    fpf: !avldiff_v (key, itm, n, h, chld, dir, rt, rtp, slf)
           >> avldiff_v (key, itm, n, h, chld1, dir, rt, rtp, slf)
    // end of [fpf]
  | p: ptr slf, dir: int dir, pc1: ptr chld1
  ) :<> void =
  if dir = 0 then let
    prval B1L (pf_at, fpf1, pf2) = fpf
    val () = p->left := pc1
    prval () = fpf := B1L (pf_at, fpf1, pf2)
  in
    // nothing
  end else let
    prval B1R (pf_at, pf1, fpf2) = fpf
    val () = p->right := pc1
    prval () = fpf := B1R (pf_at, pf1, fpf2)
  in
    // nothing
  end // end of [if]
// end of [avldiff_child_set]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
  avltree_split {h0:nat} {rt:addr} (
    pf: avltree_v (key, itm, h0, null, rt)
  | p: &ptr rt >> ptr slf, k0: key, dir: &int 0 >> int dir, cmp: cmp key
  ) :<> #[dir:two;slf:addr] [h1:nat | h1 <= h0;chld:addr] (
    avldiff_v (key, itm, h0, h1, chld, dir, rt, null, slf), avltree_v (key, itm, h1, slf, chld)
  | ptr chld
  )
// end of [avltree_split]

implement{key,itm} avltree_split
  {h0} {rt} (pf | p, k0, dir, cmp) = let
  fun loop {h:nat | h <= h0}
    {chld:addr} {dir:two} {slf:addr} .<h>. (
      fpf: avldiff_v (key, itm, h0, h, chld, dir, rt, null, slf),
      pf: avltree_v (key, itm, h, slf, chld)
    | p: &ptr slf >> ptr slf, pc: ptr chld, dir: &int dir >> int dir
  ) :<cloref> #[dir:two;slf:addr]
    [h1:nat | h1 <= h] [chld:addr] (
    avldiff_v (key, itm, h0, h1, chld, dir, rt, null, slf), avltree_v (key, itm, h1, slf, chld)
  | ptr chld
  ) =
  if pc <> null then let
    prval B (pf_at, pf_l, pf_r) = pf
    val sgn = compare_key_key (k0, pc->key, cmp)
  in
    if sgn < 0 then let
      val () = p := pc
      val () = dir := 0(*left*)
      val pc_l = pc->left
    in
      loop (B1L {key,itm} (pf_at, fpf, pf_r), pf_l | p, pc_l, dir)
    end else if sgn > 0 then let
      val () = p := pc
      val () = dir := 1(*right*)
      val pc_r = pc->right
    in
      loop (B1R {key,itm} (pf_at, pf_l, fpf), pf_r | p, pc_r, dir)
    end else // sgn = 0
      (fpf, B (pf_at, pf_l, pf_r) | pc)
    // end of [if]
  end else
    (fpf, pf | pc)
  (* end of [if] *)
  val pc = p
  val () = p := null
  prval fpf = E1 ()
in
  loop (fpf, pf | p, pc, dir)
end // end of [avltree_split]

(* ****** ****** *)

assume map_vt (key:t0p, itm:vt0p) =
  [h:nat;slf:addr] (avltree_v (key, itm, h, null, slf) | ptr slf)
// end of [map_vt]

(* ****** ****** *)

implement{} linmap_empty {key,itm} () = (E {key,itm} {null} () | null)

implement{}
  linmap_empty_free {key,itm} (m) = let
  viewtypedef map_vt = map_vt (key, itm) in
  if m.1 <> null then let
    prval () = opt_some {map_vt} (m) in true
  end else let
    prval E () = m.0; prval () = opt_none {map_vt} (m) in false
  end (* end of [if] *)
end (* end of [linmap_empty_free] *)

(* ****** ****** *)

implement{} linmap_is_empty (m) = (m.1 = null)
implement{} linmap_isnot_empty (m) = (m.1 <> null)

(* ****** ****** *)

implement{key,itm}
  linmap_height (t) = let val p = t.1 in
  if p <> null then let
    prval B (pf_at, pf_l, pf_r) = t.0
    val h = p->height
    prval () = t.0 := B (pf_at, pf_l, pf_r)
  in
    h
  end else 0 // end of [if]
end // end of [linmap_height]

(* ****** ****** *)

implement{key,itm}
  linmap_size (t) = aux (t.0 | t.1) where {
  fun aux {h:nat} {pnt,slf:addr} .<h>.
    (pf: !avltree_v (key, itm, h, pnt, slf) | p: ptr slf):<> Nat =
    if p <> null then let
      prval B (pf_at, pf_l, pf_r) = pf
      val res = aux (pf_l | p->left) + 1 + aux (pf_r | p->right)
      prval () = pf := B (pf_at, pf_l, pf_r)
    in
      res
    end else 0 // end of [if]
  // end of [aux]
} // end of [linmap_size]

(* ****** ****** *)

extern fun{key,itm:t0p}
  linmap_search {l_res:addr} (
    m: !map_vt (key, itm), k0: key, res: &itm? >> opt (itm, tag), cmp: cmp key
  ) :<> #[tag:bool] bool tag
// end of [linmap_search]

implement{key,itm} linmap_search {l_res}
  (m, k0, res, cmp) = search (m.0 | m.1, res) where {
  fun search {h:nat} {pnt:addr} {slf:addr} .<h>. (
      pf: !avltree_v (key, itm, h, pnt, slf)
    | p: ptr slf, res: &itm? >> opt (itm, tag)
    ) :<cloref> #[tag:bool] bool tag =
    if p <> null then let
      prval B (pf_at, pf_l, pf_r) = pf
      val sgn = compare_key_key (k0, p->key, cmp)
    in
      if sgn < 0 then let
        val tag = search (pf_l | p->left, res)
        prval () = pf := B (pf_at, pf_l, pf_r)
      in
        tag
      end else if sgn > 0 then let
        val tag = search (pf_r | p->right, res)
        prval () = pf := B (pf_at, pf_l, pf_r)
      in
        tag
      end else let
        val () = res := p->itm
        prval () = opt_some {itm} (res)
        prval () = pf := B (pf_at, pf_l, pf_r)
      in
        true // item associated with the given key [k0] is found
      end // end of [if]
    end else let
      prval () = opt_none {itm} (res) in false
    end // end of [if]
} // end of [linmap_search]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p} balanceIns
  {n0,h0:nat | h0 <= n0}
  {h1:nat | h0 <= h1; h1 <= h0+1}
  {chld0,chld1:addr} {dir:two} {rt:addr}
  {slf:addr} (
    fpf: avldiff_v (key, itm, n0, h0, chld0, dir, rt, null, slf)
  , pf0: avltree_v (key, itm, h1, slf, chld1) // view for the missing avltree
  | h0: int h0, pc0: ptr chld0, dir: int dir, pt: ptr rt, p: ptr slf
  , pc1: ptr chld1
  ) :<> [n1:nat;slf:addr | n0 <= n1; n1 <= n0+1] 
    (avltree_v (key, itm, n1, null, slf) | ptr slf)
// end of [balanceIns]

implement{key,itm} balanceIns
  (fpf, pf0 | h0, pc0, dir, pt, p, pc1) =
  if p <> null then let
    val h1 = avltree_height_get (pf0 | pc1)
  in
    case+ 0 of
    | _ when h0 = h1 => (
        avldiff_avltree_join {key,itm} (fpf, pf0) | pt
      ) where {
        val () = avldiff_child_set<key,itm> (fpf | p, dir, pc1)
      } (* end of [_ when ...] *)
    | _ => let
(*
        h1 = h0 + 1
*)
      in
        if dir = 0 then let
          prval B1L (pf_at, fpf1, pf2) = fpf
          val pp = p->parent
          val h0p = p->height
          val dirp = avldiff_dir_get (fpf1 | pp, p)
          val () = p->left := pc1
          val h0r = avltree_height_get<key,itm> (pf2 | p->right)
        in
          if h1 = h0r + 2 then let
            val (pf0_new | p_new) =
              avltree_rrotate<key,itm> (pf_at, pf0, pf2 | p)
            // end of [val]
          in
            balanceIns<key,itm> (fpf1, pf0_new | h0p, p, dirp, pt, pp, p_new)
          end else let
            val () = p->height := max (h1, h0r) + 1
            prval pf0_new = B {key,itm} (pf_at, pf0, pf2)
          in
            balanceIns<key,itm> (fpf1, pf0_new | h0p, p, dirp, pt, pp, p)
          end // end of [if]
        end else let
          prval B1R (pf_at, pf1, fpf2) = fpf
          val pp = p->parent
          val h0p = p->height
          val dirp = avldiff_dir_get (fpf2 | pp, p)
          val () = p->right := pc1
          val h0l = avltree_height_get<key,itm> (pf1 | p->left)
        in
          if h1 = h0l + 2 then let
            val (pf0_new | p_new) =
              avltree_lrotate<key,itm> (pf_at, pf1, pf0 | p)
            // end of [val]
          in
            balanceIns<key,itm> (fpf2, pf0_new | h0p, p, dirp, pt, pp, p_new)
          end else let
            val () = p->height := max (h0l, h1) + 1
            prval pf0_new = B {key,itm} (pf_at, pf1, pf0)
          in
            balanceIns<key,itm> (fpf2, pf0_new | h0p, p, dirp, pt, pp, p)
          end // end of [if]
        end (* end of [if] *)
      end (* end of [_] *)
  end else let
    prval E1 () = fpf in (pf0 | pc1)
  end // end of [if]
// end of [balanceIns]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
linmap_insert {l_at:addr} (
    pf_at: !avlnode (key, itm) @ l_at >> option_v (avlnode (key, itm) @ l_at, tag)
  | m: &map_vt (key, itm), p_at: ptr l_at, cmp: cmp key
  ) :<> #[tag:bool] bool tag
// end of [linmap_insert]

implement{key,itm}
  linmap_insert {l_at} (pf_at | m, p_at, cmp) = let
//
  prval () = lemma (pf_at) where {
    extern prfun lemma (pf: !avlnode (key, itm) @ l_at):<prf> [l_at <> null] void
  } // end of [prval]
//
  val pt = m.1
  var p = pt
  val k0 = p_at->key
  var dir: int = 0
  val (fpf, pf0 | pc0) = avltree_split (m.0 | p, k0, dir, cmp)
in
  if pc0 <> null then let
    prval pf = avldiff_avltree_join {key,itm} (fpf, pf0)
    prval () = pf_at := Some_v (pf_at)
  in
    m.0 := pf; true (*tag*) // no insertion is performed
  end else let
    prval E () = pf0
    val () = p_at->height := 1
    val () = p_at->parent := p
    val () = p_at->left := null
    val () = p_at->right := null
    prval pf0 = B {key,itm} (pf_at, E (), E ())
    prval () = pf_at := None_v ()
    val (pf | p_new) = balanceIns<key,itm> (fpf, pf0 | 0, pc0, dir, pt, p, p_at)
  in
    m.0 := pf; m.1 := p_new; false (*tag*) // insertion is performed
  end // end of [if]
end (* end of [linmap_insert] *)

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p} balanceRem
  {n0,h0:nat | h0 <= n0}
  {h1:nat | h1 <= h0; h0 <= h1+1}
  {chld0,chld1:addr} {dir:two} {rt:addr}
  {slf:addr} (
    fpf: avldiff_v (key, itm, n0, h0, chld0, dir, rt, null, slf)
  , pf0: avltree_v (key, itm, h1, slf, chld1) // view for the missing avltree
  | h0: int h0, pc0: ptr chld0, dir: int dir, pt: ptr rt, p: ptr slf
  , pc1: ptr chld1
  ) :<> [n1:nat;slf:addr | n1 <= n0; n0 <= n1+1]
    (avltree_v (key, itm, n1, null, slf) | ptr slf)
// end of [balanceRem]

implement{key,itm} balanceRem
  (fpf, pf0 | h0, pc0, dir, pt, p, pc1) =
  if p <> null then let
    val h1 = avltree_height_get (pf0 | pc1)
  in
    case+ 0 of
    | _ when h0 = h1 => (
        avldiff_avltree_join {key,itm} (fpf, pf0) | pt
      ) where {
        val () = avldiff_child_set<key,itm> (fpf | p, dir, pc1)
      } (* end of [_ when ...] *)
    | _ => let
(*
        h0 = h1 + 1
*)
      in
        if dir = 0 then let
          prval B1L (pf_at, fpf1, pf2) = fpf
          val pp = p->parent
          val h0p = p->height
          val dirp = avldiff_dir_get (fpf1 | pp, p)
          val () = p->left := pc1
          val h0r = avltree_height_get<key,itm> (pf2 | p->right)
        in
          if h0r = h1 + 2 then let
            val (pf0_new | p_new) =
              avltree_lrotate<key,itm> (pf_at, pf0, pf2 | p)
            // end of [val]
          in
            balanceRem<key,itm> (fpf1, pf0_new | h0p, p, dirp, pt, pp, p_new)
          end else let
            val () = p->height := max (h1, h0r) + 1
            prval pf0_new = B {key,itm} (pf_at, pf0, pf2)
          in
            balanceRem<key,itm> (fpf1, pf0_new | h0p, p, dirp, pt, pp, p)
          end // end of [if]
        end else let
          prval B1R (pf_at, pf1, fpf2) = fpf
          val pp = p->parent
          val h0p = p->height
          val dirp = avldiff_dir_get (fpf2 | pp, p)
          val () = p->right := pc1
          val h0l = avltree_height_get<key,itm> (pf1 | p->left)
        in
          if h0l = h1 + 2 then let
            val (pf0_new | p_new) =
              avltree_rrotate<key,itm> (pf_at, pf1, pf0 | p)
            // end of [val]
          in
            balanceRem<key,itm> (fpf2, pf0_new | h0p, p, dirp, pt, pp, p_new)
          end else let
            val () = p->height := max (h0l, h1) + 1
            prval pf0_new = B {key,itm} (pf_at, pf1, pf0)
          in
            balanceRem<key,itm> (fpf2, pf0_new | h0p, p, dirp, pt, pp, p)
          end // end of [if]
        end (* end of [if] *)
      end (* end of [_] *)
  end else let
    prval E1 () = fpf in (pf0 | pc1)
  end // end of [if]
// end of [balanceRem]

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p} avltree_avltree_join
  {hl,hr:nat | hl <= hr+1; hr <= hl+1} {lft,rgh,pnt1,pnt2:addr} (
    pf_l: avltree_v (key, itm, hl, pnt1, lft), pf_r: avltree_v (key, itm, hr, pnt2, rgh)
  | p_l: ptr lft, p_r: ptr rgh
  ) :<> [h:int | max(hl,hr) <= h; h <= max(hl,hr)+1]
    [pnt,slf:addr] (avltree_v (key, itm, h, pnt, slf) | ptr slf)
// end of [avltree_avltree_join]

viewtypedef avlnode
  (key:t@ype, itm:viewt@ype, lft: addr) =
  [h:nat] [rgh,pnt:addr] avlnode (key, itm, h, lft, rgh, pnt)

implement{key,itm} avltree_avltree_join
  {hl,hr} {lft,rgh,pnt1,pnt2} (pf_l, pf_r | p_l, p_r) = let
  fun loop {h0:nat | h0 <= hl}
    {chld:addr | chld <> null} {rt:addr} {slf:addr} .<h0>. (
      fpf: avldiff_v (key, itm, hl, h0, chld, 1(*right*), rt, null, slf)
    , pf0: avltree_v (key, itm, h0, slf, chld) // view for the missing avltree
    | pc: ptr (chld), pt: ptr rt, p: ptr slf
    ) :<> [slf:addr | slf <> null]
      [hl1:nat | hl1 <= hl; hl <= hl1+1] [lft:addr]  (
      avlnode (key, itm, lft) @ slf, avltree_v (key, itm, hl1, slf, lft) | ptr slf
    ) = let
    prval B (pf0_at, pf0_l, pf0_r) = pf0
    val pc_r = pc->right
  in
    if pc_r <> null then let
      prval fpf = B1R {key,itm} (pf0_at, pf0_l, fpf)
    in
      loop (fpf, pf0_r | pc_r, pt, pc)
    end else let
      prval E () = pf0_r
      val pc_l = pc->left
      val () = avltree_parent_set<key,itm> (pf0_l | pc_l, p)
      val (pf | pt) = balanceRem<key,itm>
        (fpf, pf0_l | pc->height, pc, 1(*right*), pt, p, pc_l)
      val () = pc->left := pt
      val () = avltree_parent_set<key,itm> (pf | pt, pc)
    in
      (pf0_at, pf | pc)
    end (* end of [if] *)
  end // end of [loop]
in
  if p_l <> null then let
    prval fpf = E1 ()
    val () = avltree_parent_set (pf_l | p_l, null)
    val (pf_at, pf_l | p_at) = loop (fpf, pf_l | p_l, p_l, null)
    val () = p_at->right := p_r
    val () = avltree_parent_set<key,itm> (pf_r | p_r, p_at)
    val p_l = p_at->left
    val hl = avltree_height_get<key,itm> (pf_l | p_l)
    val hr = avltree_height_get<key,itm> (pf_r | p_r)
  in
    if hl+2 = hr then
      avltree_lrotate<key,itm> (pf_at, pf_l, pf_r | p_at)
    else let
      val () = p_at->height := max(hl,hr) + 1
    in
      (B (pf_at, pf_l, pf_r) | p_at)
    end (* end of [if] *)
  end else let
    prval E () = pf_l in (pf_r | p_r)
  end // end of [if]
end (* end of [avltree_avltree_join] *)

(* ****** ****** *)

extern
fun{key:t0p;itm:vt0p}
linmap_remove {l_at:addr} (
    m: &map_vt (key, itm), k0: key, cmp: cmp key
  ) :<> [l_at:addr] (
    option_v (avlnode (key, itm) @ l_at, l_at <> null) | ptr l_at
  )
// end of [linmap_remove]

implement{key,itm}
  linmap_remove {l_at} (m, k0, cmp) = let
  val pt = m.1
  var p = pt
  var dir: int = 0
  val [h1:int,chld:addr]
    (fpf, pf0 | pc0) = avltree_split (m.0 | p, k0, dir, cmp)
  // end of [val]
  viewdef V = avlnode (key,itm) @ chld
in
  if pc0 <> null then let
    prval B (pf0_at, pf0_l, pf0_r) = pf0
    val (pf0 | pc0_new) =
      avltree_avltree_join<key,itm> (pf0_l, pf0_r | pc0->left, pc0->right)
    // end of [val]
    val () = avltree_parent_set (pf0 | pc0_new, p)
    val [n1:int,_:addr] (pf_new | pt_new) =
      balanceRem<key,itm> (fpf, pf0 | pc0->height, pc0, dir, pt, p, pc0_new)
    // end of [val]
  in
    m.0 := pf_new; m.1 := pt_new; (Some_v {V} (pf0_at) | pc0) // removal
  end else let
    prval pf = avldiff_avltree_join {key,itm} (fpf, pf0)
  in
    m.0 := pf; (None_v {V} () | null) // no removal is performed
  end // end of [if]
end (* end of [linmap_remove] *)

(* ****** ****** *)

// infix order foreach
fun{key:t0p;itm:vt0p} avltree_foreach_inf
  {v:view} {vt:viewtype} {h:nat} {pnt,slf:addr} {f:eff} .<h>. (
    pf1: !avltree_v (key,itm,h,pnt,slf)
  , pf2: !v
  | p: ptr slf
  , f: (!v | key, &itm, !vt) -<f> void
  , env: !vt
  ) :<f> void = let
in
  if p <> null then let
    prval B (pf1_at, pf1_l, pf1_r) = pf1
    val () = avltree_foreach_inf (pf1_l, pf2 | p->left, f, env)
    val () = f (pf2 | p->key, p->itm, env)
    val () = avltree_foreach_inf (pf1_r, pf2 | p->right, f, env)
    prval () = pf1 := B (pf1_at, pf1_l, pf1_r)
  in
    // nothing
  end // end of [if]
end // end of [bst_foreach_inf]

(* ****** ****** *)

extern fun{key:t0p;itm:vt0p} linmap_foreach_clo {v:view}
  (pf: !v | xs: !map_vt (key, itm), f: &(!v | key, &itm) -<clo> void):<> void

implement{key,itm}
  linmap_foreach_clo {v} (pf1 | m, f) = let
  viewtypedef clo_t = (!v | key, &itm) -<clo> void
  stavar l_f: addr; val p_f: ptr l_f = &f
  viewdef V = (v, clo_t @ l_f)
  fn app (pf: !V | k: key, i: &itm, p_f: !ptr l_f):<> void = let
    prval (pf1, pf2) = pf
    val () = !p_f (pf1 | k, i)
    prval () = pf := (pf1, pf2)
  in
    // empty
  end // end of [app]
  prval pf2 = view@ f; prval pf = (pf1, pf2)
  val () = avltree_foreach_inf<key,itm> {V} {ptr l_f} (m.0, pf | m.1, app, p_f)
  prval () = (pf1 := pf.0; view@ f := pf.1)
in
  // empty
end // end of [linmap_foreach_clo]

(* ****** ****** *)

(*

// for the purpose of debugging

extern
fun{key:t0p;itm:vt0p}
print_avltree {h:nat} {pnt,slf:addr}
  (pf: !avltree_v (key,itm,h,pnt,slf) | p: ptr slf): void
  = "print_avltree"

extern
fun{key:t0p;itm:vt0p}
print_avltree_dummy {slf:addr} (p: ptr slf): void
  = "print_avltree"

extern fun{key:t0p;itm:vt0p} print_linmap (map: !map_vt (key,itm)): void

implement{key,itm} print_linmap (map) = print_avltree (map.0 | map.1)

*)

(* ****** ****** *)

(* end of [linmap_avltree_ngc.dats] *)
