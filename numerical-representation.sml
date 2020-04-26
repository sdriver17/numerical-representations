signature RANDOMACCESSLIST =
sig

  type 'a RList

  val empty : 'a RList
  val isEmpty : 'a RList -> bool

  val cons : 'a * 'a RList -> 'a RList
  (* head and tail raise Empty if list is empty*)
  val head : 'a RList -> 'a
  val tail : 'a RList -> 'a RList

  (* Lookup and Update raise subscript if index is out of bounds*)
  val lookup : int * 'a RList -> 'a
  val update : int * 'a * 'a RList -> 'a RList
end

structure DenseBinary =
struct

  exception EMPTY
  exception SUBSCRIPT

  datatype digit = ZERO | ONE
  type nat = digit list (*increasing order of significance*)

  fun inc [] = [ONE]
    | inc (ZERO :: ds) = ONE :: ds
    | inc (ONE :: ds) = ZERO :: inc ds

  fun dec [] = raise EMPTY
    | dec [ONE] = []
    | dec (ONE :: ds) = ZERO :: ds
    | dec (ZERO :: ds) = ONE :: dec ds

  fun add (ds, []) = ds
    | add ([], ds) = ds
    | add (d :: ds1, ZERO :: ds2) = d :: add (ds1,ds2)
    | add (ZERO :: ds1, d :: ds2) = d :: add (ds1,ds2)
    | add (ONE :: ds1, ONE :: ds2) = ZERO :: inc (add (ds1, ds2))

end

structure SPARSEBinary =
struct

  exception EMPTY
  exception SUBSCRIPT

  type nat = int list (*increasing list of weights*)

  fun carry (w, []) = [w]
    | carry (w, ws as w':: ws') = if w < w' then w :: ws
                                            else carry (2*w, ws')

  fun borrow (w, ws as w':: ws') = if w = w' then ws'
                                             else w :: borrow (2*w, ws)

  fun inc ws = carry (1, ws)
  fun dec ws = borrow (1, ws)

  fun add (ws, []) = ws
    | add ([], ws) = ws
    | add (m as w1 :: ws1, n as w2 :: ws2) = if w1 < w2 then w1 :: add(ws1,n)
                                        else if w2 < w1 then w2 :: add(m, ws2)
                                        else carry (2*w1, add(ws1, ws2))

end

structure BinaryRAL : RANDOMACCESSLIST =
struct

  exception EMPTY
  exception SUBSCRIPT

  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a Digit = ZERO | ONE of 'a Tree
  type 'a RList = 'a Digit list

  val empty = []
  fun isEmpty ts = null ts


  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1,t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t, []) = [ONE t]
    | consTree (t, ZERO :: ts) = ONE t:: ts
    | consTree (t1, ONE t2 :: ts) = ZERO :: consTree (link (t1, t2), ts)
  fun unconsTree [] = raise EMPTY
    | unconsTree [ONE t] = (t, [])
    | unconsTree (ONE t:: ts) = (t, ZERO :: ts)
    | unconsTree (ZERO :: ts) = let
                                  val (NODE (_, t1, t2), ts') = unconsTree ts
                                in
                                  (t1, ONE t2 :: ts')
                                end


  fun cons (x, ts) = consTree (LEAF x, ts)
  fun head ts = let val (LEAF x, _) = unconsTree ts in x end
  fun tail ts = let val (_, ts') = unconsTree ts in ts' end

  fun lookupTree (0, LEAF x) = x
    | lookupTree (i, LEAF x) = raise SUBSCRIPT
    | lookupTree (i, NODE (w, t1, t2)) = if i < w div 2 then lookupTree (i, t1)
                                                        else lookupTree (i - w div 2, t2)
  fun updateTree (0, y, LEAF x) = LEAF y
    | updateTree (i, y, LEAF x) = raise SUBSCRIPT
    | updateTree (i, y, NODE (w, t1, t2)) = if i < w div 2 then NODE (w, updateTree (i, y, t1), t2)
                                                           else NODE (w, t1, updateTree (i - w div 2, y, t2))

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, ZERO :: ts) = lookup (i, ts)
    | lookup (i, ONE t :: ts) = if i < size t then lookupTree (i, t) else lookup (i - size t, ts)

  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, ZERO :: ts) = ZERO :: update (i, y, ts)
    | update (i, y, ONE t :: ts) = if i < size t then ONE(updateTree (i,y,t)) :: ts
                                                else ONE t :: update(i - size t, y, ts)

end

(*Implemet a sparse version of binary RAL*)

structure Susp360 :> SUSP =
struct

  (*  Remember:  if e : int, then Thunk(fn () => e) : int th_or_res
  *                               Result(9) : int th_or_res
  *)
  datatype 'a th_or_res = Thunk of unit -> 'a
                        | Result of 'a

  type 'a susp = 'a th_or_res ref

  fun $(e : unit -> 'a) : 'a susp =
    ref(Thunk e)

  val delay : (unit -> 'a) -> 'a susp = $

  fun force (s : 'a susp) : 'a =
    case !s of
         Thunk e =>
         let
           val v = e()
           val () = s := Result v
         in
           v
         end
       | Result v => v

end

structure ZerolessBinaryRAL : RANDOMACCESSLIST =
struct

  exception EMPTY
  exception SUBSCRIPT

  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a Digit = ONE of 'a Tree | TWO of 'a Tree * 'a Tree
  type 'a RList = 'a Digit list

  val empty = []
  fun isEmpty ts = null ts

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1,t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t, []) = [ONE t]
    | consTree (t, ONE t2 :: ts) = TWO (t,t2) :: ts
    | consTree (t1, TWO (t2,t3) :: ts) = ONE t1 :: consTree (link (t2, t3), ts)
  fun unconsTree [] = raise EMPTY
    | unconsTree [ONE t] = (t, [])
    | unconsTree (TWO (t1,t2):: ts) = (t1, ONE t2 :: ts)
    | unconsTree (ONE t :: ts) = (t, ts)

  fun cons (x, ts) = consTree (LEAF x, ts)
  fun head (ONE(LEAF x) :: _) = x
    | head (TWO(LEAF x, LEAF y) :: _) = x
    | head ([]) = raise EMPTY
  fun tail ts = let val (_, ts') = unconsTree ts in ts' end

  fun lookupTree (0, LEAF x) = x
    | lookupTree (i, LEAF x) = raise SUBSCRIPT
    | lookupTree (i, NODE (w, t1, t2)) = if i < w div 2 then lookupTree (i, t1)
                                                        else lookupTree (i - w div 2, t2)
  fun updateTree (0, y, LEAF x) = LEAF y
    | updateTree (i, y, LEAF x) = raise SUBSCRIPT
    | updateTree (i, y, NODE (w, t1, t2)) = if i < w div 2 then NODE (w, updateTree (i, y, t1), t2)
                                                           else NODE (w, t1, updateTree (i - w div 2, y, t2))

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, ONE t :: ts) = if i < size t then lookupTree (i, t) else lookup (i - size t, ts)
    | lookup (i, (TWO (t1,t2)) :: ts) = if i < size t1 then lookupTree (i ,t1) else lookup (i - size t1, ONE t2 :: ts)

  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, ONE t :: ts) = if i < size t then ONE(updateTree (i,y,t)) :: ts
                                                else ONE t :: update(i - size t, y, ts)
    | update (i, y, (TWO (t1,t2)) :: ts) = if i < size t1 then TWO(updateTree(i,y,t1),t2) :: ts
                                                          else if i - size t1 < size t2 then TWO(t1,updateTree(i - size t1,y,t2)) :: ts
                                                                                        else TWO (t1,t2) :: update (i - size t1 - size t2, y, ts)

end

(* functor ZerolessRedundantLazyBinaryRAL (S : SUSP) : RANDOMACCESSLIST =
struct

  exception EMPTY
  exception SUBSCRIPT

  datatype 'a streamcell = Nil | Cons of 'a * 'a stream
  withtype 'a stream = 'a streamcell S.susp

  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a Digit = ONE of 'a Tree | TWO of 'a Tree * 'a Tree | THREE of 'a Tree * 'a Tree * 'a Tree
  type 'a RList = 'a Digit stream

  val empty = Nil
  fun isEmpty ts = null ts

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1,t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t, []) = [ONE t]
    | consTree (t, ONE t2 :: ts) = TWO (t,t2) :: ts
    | consTree (t1, TWO (t2,t3) :: ts) = ONE t1 :: consTree (link (t2, t3), ts)
  fun unconsTree [] = raise EMPTY
    | unconsTree [ONE t] = (t, [])
    | unconsTree (TWO (t1,t2):: ts) = (t1, ONE t2 :: ts)
    | unconsTree (ONE t :: ts) = (t, ts)

  fun cons (x, ts) = consTree (LEAF x, ts)
  fun head (ONE(LEAF x) :: _) = x
    | head (TWO(LEAF x, LEAF y) :: _) = x
    | head ([]) = raise EMPTY
  fun tail ts = let val (_, ts') = unconsTree ts in ts' end

  fun lookupTree (0, LEAF x) = x
    | lookupTree (i, LEAF x) = raise SUBSCRIPT
    | lookupTree (i, NODE (w, t1, t2)) = if i < w div 2 then lookupTree (i, t1)
                                                        else lookupTree (i - w div 2, t2)
  fun updateTree (0, y, LEAF x) = LEAF y
    | updateTree (i, y, LEAF x) = raise SUBSCRIPT
    | updateTree (i, y, NODE (w, t1, t2)) = if i < w div 2 then NODE (w, updateTree (i, y, t1), t2)
                                                           else NODE (w, t1, updateTree (i - w div 2, y, t2))

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, ONE t :: ts) = if i < size t then lookupTree (i, t) else lookup (i - size t, ts)
    | lookup (i, (TWO (t1,t2)) :: ts) = if i < size t1 then lookupTree (i ,t1) else lookup (i - size t1, ONE t2 :: ts)

  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, ONE t :: ts) = if i < size t then ONE(updateTree (i,y,t)) :: ts
                                                else ONE t :: update(i - size t, y, ts)
    | update (i, y, (TWO (t1,t2)) :: ts) = if i < size t1 then TWO(updateTree(i,y,t1),t2) :: ts
                                                          else if i - size t1 < size t2 then TWO(t1,updateTree(i - size t1,y,t2)) :: ts
                                                                                        else TWO (t1,t2) :: update (i - size t1 - size t2, y, ts)

end *)

structure ZerolessRedundantBinaryRAL : RANDOMACCESSLIST =
struct

  exception EMPTY
  exception SUBSCRIPT

  datatype 'a Tree = LEAF of 'a | NODE of int * 'a Tree * 'a Tree
  datatype 'a Digit = ONE of 'a Tree | TWO of 'a Tree * 'a Tree | THREE of 'a Tree * 'a Tree * 'a Tree
  type 'a RList = 'a Digit list

  val empty = []
  fun isEmpty ts = null ts

  fun size (LEAF x) = 1
    | size (NODE (w, t1, t2)) = w
  fun link (t1,t2) = NODE (size t1 + size t2, t1, t2)
  fun consTree (t, []) = [ONE t]
    | consTree (t, ONE t2 :: ts) = TWO (t,t2) :: ts
    | consTree (t, TWO (t2,t3) :: ts) = THREE(t,t2,t3) :: ts
    | consTree (t, THREE(t2,t3,t4) :: ts) = ONE(t) :: consTree(link(t2,link(t3,t4)),ts)
  fun unconsTree [] = raise EMPTY
    | unconsTree [ONE t] = (t, [])
    | unconsTree (THREE (t1,t2,t3) :: ts) = (t1, TWO(t2,t3) :: ts)
    | unconsTree (TWO (t1,t2):: ts) = (t1, ONE t2 :: ts)
    | unconsTree (ONE t :: ts) = (t, ts)

  fun cons (x, ts) = consTree (LEAF x, ts)
  fun head (ONE(LEAF x) :: _) = x
    | head (TWO(LEAF x, LEAF y) :: _) = x
    | head (THREE(LEAF x, LEAF y, LEAF z) :: _) = x
    | head ([]) = raise EMPTY
  fun tail ts = let val (_, ts') = unconsTree ts in ts' end

  fun lookupTree (0, LEAF x) = x
    | lookupTree (i, LEAF x) = raise SUBSCRIPT
    | lookupTree (i, NODE (w, t1, t2)) = if i < w div 2 then lookupTree (i, t1)
                                                        else lookupTree (i - w div 2, t2)
  fun updateTree (0, y, LEAF x) = LEAF y
    | updateTree (i, y, LEAF x) = raise SUBSCRIPT
    | updateTree (i, y, NODE (w, t1, t2)) = if i < w div 2 then NODE (w, updateTree (i, y, t1), t2)
                                                           else NODE (w, t1, updateTree (i - w div 2, y, t2))

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, ONE t :: ts) = if i < size t then lookupTree (i, t) else lookup (i - size t, ts)
    | lookup (i, (TWO (t1,t2)) :: ts) = if i < size t1 then lookupTree (i ,t1) else lookup (i - size t1, ONE t2 :: ts)

  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, ONE t :: ts) = if i < size t then ONE(updateTree (i,y,t)) :: ts
                                                else ONE t :: update(i - size t, y, ts)
    | update (i, y, (TWO (t1,t2)) :: ts) = if i < size t1 then TWO(updateTree(i,y,t1),t2) :: ts
                                                          else if i - size t1 < size t2 then TWO(t1,updateTree(i - size t1,y,t2)) :: ts
                                                                                        else TWO (t1,t2) :: update (i - size t1 - size t2, y, ts)

end

structure SkewBinaryRAL: RANDOMACCESSLIST =
struct

  exception EMPTY
  exception SUBSCRIPT

  datatype 'a Tree = LEAF of 'a | NODE of 'a * 'a Tree * 'a Tree
  type 'a RList = (int * 'a Tree) list (* integer is the weight of the tree *)

  val empty = []
  fun isEmpty ts = null ts

  fun cons (x, ts as (w1, t1) :: (w2, t2) :: ts') = if w1 = w2 then (1+w1+w2, NODE (x, t1, t2)):: ts' else (1, LEAF x) :: ts
    | cons(x,ts) = (1,LEAF x) :: ts

  fun head [] = raise EMPTY
    | head((1, LEAF x) :: ts) = x
    | head ((w, NODE (x,t1,t2)) :: ts) = x
  fun tail [] = raise EMPTY
    | tail ((1, LEAFX):: ts) = ts
    | tail((w, NODE(x,t1,t2)) :: ts) = (w div 2, t1) :: (w div 2, t2) :: ts

  fun lookupTree (1, 0, LEAF x) = x
    | lookupTree (1, i, LEAF x) = raise SUBSCRIPT
    | lookupTree (w, 0, NODE (x, t1, t2)) = x
    | lookupTree (w, i, NODE (x, t1, t2)) = if i <= w div 2 then lookupTree(w div 2, i - 1, t1)
                                                            else lookupTree(w div 2, i - 1 - w div 2, t2)

  fun updateTree (1, 0, y, LEAF x) = LEAF y
    | updateTree (1, i, y, LEAF x) = raise SUBSCRIPT
    | updateTree (w, 0, y, NODE (x, t1, t2)) = NODE (y, t1, t2)
    | updateTree (w, i, y, NODE (x, t1, t2)) = if i <= w div 2 then NODE (x, updateTree (w div 2, i - 1 , y, t1), t2)
                                                               else NODE (x, t1, updateTree(w div 2, i - 1 - w div 2, y, t2))

  fun lookup (i, []) = raise SUBSCRIPT
    | lookup (i, (w, t):: ts) = if i < w then lookupTree (w, i, t)
                                         else lookup (i - w, ts)

  fun update (i, y, []) = raise SUBSCRIPT
    | update (i, y, (w, t) :: ts) = if i < w then (w, updateTree (w, i, y, t)) :: ts
                                             else (w, t) :: update (i - w, y, ts)
end

functor SkewBinomialHeap (Element: ORD_KEY) =
struct

    exception EMPTY
    exception SUBSCRIPT

    structure Elem = Element
    datatype Tree = NODE of int * Elem.ord_key * Elem.ord_key list * Tree list
    type Heap = Tree list

    val empty = []
    fun isEmpty ts = null ts

    fun rank (NODE (r, x, xs, c)) = r
    fun root (NODE (r, x, xs, c)) = x
    fun link (t1 as NODE (r, x1, xs1, c1),
              t2 as NODE (_, x2, xs2, c2)) = case Elem.compare (x1, x2) of
                                               LESS => NODE (r+1, x1, xs1, t2 :: c1)
                                              |EQUAL => NODE (r+1, x1, xs1, t2 :: c1)
                                              |GREATER => NODE (r+1, x2, xs2, t1 :: c2)

    fun skewLink (x, t1, t2) = let
                                 val NODE (r, y, ys, c) = link (t1, t2)
                               in
                                 case Elem.compare(x,y) of
                                    LESS => NODE (r, x, y :: ys, c)
                                   |EQUAL => NODE (r, x, y :: ys, c)
                                   |GREATER => NODE (r, y, x :: ys, c)
                               end

    fun insTree (t,[]) =[t]
      | insTree (t1, t2 :: ts) = if rank t1 < rank t2 then t1 :: t2 :: ts
                                                      else insTree(link (t1, t2), ts)

    fun mergeTrees (ts1, []) = ts1
      | mergeTrees ([], ts2) = ts2
      | mergeTrees (ts1 as t1 :: ts1',
                    ts2 as t2 :: ts2') = if rank t1 < rank t2 then t1 :: mergeTrees (ts1', ts2)
                                    else if rank t2 < rank t1 then t2 :: mergeTrees (ts1,ts2')
                                    else insTree (link (t1, t2), mergeTrees (ts1', ts2'))

    fun normalize [] = []
      | normalize (t :: ts) = insTree (t,ts)

    fun insert (x, ts as t1 :: t2 :: rest) = if rank t1 = rank t2 then skewLink (x, t1, t2) :: rest
                                                                  else NODE (0, x, [],[]) :: ts
      | insert (x, ts) = NODE (0, x, [],[]) :: ts

    fun merge (ts1, ts2) = mergeTrees (normalize ts1, normalize ts2)

    fun removeMinTree [] = raise EMPTY
      | removeMinTree [t] = (t,[])
      | removeMinTree (t :: ts) = let
                                    val (t', ts') = removeMinTree ts
                                  in
                                    case Elem.compare(root t, root t') of
                                      LESS => (t, ts)
                                    | EQUAL => (t, ts)
                                    | GREATER => (t, t' :: ts')
                                  end

    fun findMin ts = let
                       val (t, _) = removeMinTree ts
                     in
                       root t
                     end

    fun deleteMin ts = let
                         val (NODE (_, x, xs, ts1), ts2) = removeMinTree ts
                         fun insertAll([], ts) = ts
                           | insertAll(x :: xs, ts) = insertAll (xs, insert (x, ts))
                         in
                           insertAll (xs, merge (rev ts1, ts2))
                         end

end

structure intBinaryHeap = SkewBinomialHeap(struct type ord_key = int
                                                  val compare = Int.compare end)
