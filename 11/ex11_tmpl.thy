(*<*)
theory ex11_tmpl
imports
    "HOL-Data_Structures.Leftist_Heap"
begin
(*>*)
text {* \ExerciseSheet{11}{22.~6.~2018} *}

text \<open>
  \Exercise{Insert for Leftist Heap}

  \<^item> Define a function to directly insert an element into a leftist heap.
    Do not construct an intermediate heap like insert via merge does!

  \<^item> Show that your function is correct

  \<^item> Define a timing function for your insert function, and show that it is
    linearly bounded by the rank of the tree.
\<close>

fun lh_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> 'a lheap"
  where
  "lh_insert _ _ = undefined"

lemma mset_lh_insert: "mset_tree (lh_insert x t) = mset_tree t + {# x #}"
  sorry

lemma "heap t \<Longrightarrow> heap (lh_insert x t)"
  sorry

lemma "ltree t \<Longrightarrow> ltree (lh_insert x t)"
  sorry


fun t_lh_insert :: "'a::ord \<Rightarrow> 'a lheap \<Rightarrow> nat"
  where
  "t_lh_insert _ _ = undefined"

lemma "t_lh_insert x t \<le> rank t + 1"
  sorry

text \<open>
  \Exercise{Bootstrapping a Priority Queue}

  Given a generic priority queue implementation with
  \<open>O(1)\<close> \<open>empty\<close>, \<open>is_empty\<close> operations, \<open>O(f\<^sub>1 n)\<close> insert,
  and \<open>O(f\<^sub>2 n)\<close> \<open>get_min\<close> and \<open>del_min\<close> operations.

  Derive an implementation with \<open>O(1)\<close> \<open>get_min\<close>, and the
  asymptotic complexities of the other operations unchanged!

  Hint: Store the current minimal element! As you know nothing
    about \<open>f\<^sub>1\<close> and \<open>f\<^sub>2\<close>, you must not use \<open>get_min/del_min\<close>
    in your new \<open>insert\<close> operation, and vice versa!
\<close>

text \<open>For technical reasons, you have to define the new implementations type
      outside the locale!\<close>
datatype ('a,'s) bs_pq = PUT_CONSTRUCTORS_HERE

locale Bs_Priority_Queue =
  orig: Priority_Queue where
    empty = orig_empty and
    is_empty = orig_is_empty and
    insert = orig_insert and
    get_min = orig_get_min and
    del_min = orig_del_min and
    invar = orig_invar and
    mset = orig_mset
  for orig_empty orig_is_empty orig_insert orig_get_min orig_del_min orig_invar
  and orig_mset :: "'s \<Rightarrow> 'a::linorder multiset"
begin
  text \<open>In here, the original implementation is available with the prefix \<open>orig\<close>, e.g. \<close>
  term orig_empty term orig_invar
  thm orig.invar_empty

  definition empty :: "('a,'s) bs_pq"
    where "empty = undefined"

  fun is_empty :: "('a,'s) bs_pq \<Rightarrow> bool"
    where
    "is_empty _ \<longleftrightarrow> undefined"

  fun insert :: "'a \<Rightarrow> ('a,'s) bs_pq \<Rightarrow> ('a,'s) bs_pq"
    where
    "insert _ _ = undefined"

  fun get_min :: "('a,'s) bs_pq \<Rightarrow> 'a"
    where
    "get_min _ = undefined"

  fun del_min :: "('a,'s) bs_pq \<Rightarrow> ('a,'s) bs_pq"
    where
    "del_min _ = undefined"

  fun invar :: "('a,'s) bs_pq \<Rightarrow> bool"
    where
    "invar _ = undefined"

  fun mset :: "('a,'s) bs_pq \<Rightarrow> 'a multiset"
    where
    "mset _ = undefined"

  lemmas [simp] = orig.is_empty orig.mset_get_min orig.mset_del_min
    orig.mset_insert orig.mset_empty
    orig.invar_empty orig.invar_insert orig.invar_del_min

  text \<open>Show that your new implementation satisfies the priority queue interface!\<close>
  sublocale Priority_Queue empty is_empty insert get_min del_min invar mset
    apply unfold_locales
  proof goal_cases
    case 1
    then show ?case sorry
  next
    case (2 q) -- \<open>and so on\<close>
    oops


end

text\<open>
\Homework{Heap}{29.~6.~2018}

A binary tree can be encoded as an array \<open>[a\<^sub>1,...,a\<^sub>n]\<close>, such that
the parent of node \<open>a\<^sub>i\<close> is node \<open>a\<^sub>(\<^sub>i \<^sub>d\<^sub>i\<^sub>v \<^sub>2\<^sub>)\<close>.

Thus, for a heap, each node is greater than or equal to its parent:
\<close>

definition parent :: "nat \<Rightarrow> nat" where "parent i \<equiv> (i+1) div 2 - 1"
definition is_heap :: "'a::linorder list \<Rightarrow> bool"
  where "is_heap h \<equiv> \<forall>i<length h. h!i \<ge> h!parent i"


text \<open>A heap with a single defect at index \<open>j\<close> is characterized as follows:
  The heap property holds for all elements except \<open>j\<close>,
  and the children of \<open>j\<close> must also be greater than their grand-parent.
\<close>
definition is_heap_except :: "nat \<Rightarrow> 'a::linorder list \<Rightarrow> bool" where
  "is_heap_except j h \<equiv>
      (\<forall>i<length h. i\<noteq>j \<longrightarrow> h!i \<ge> h!(parent i))
    \<and> (\<forall>i<length h. parent i = j \<longrightarrow> h!i \<ge> h!(parent j))"



text \<open>
  The function \<open>sift_up\<close> corrects a single defect in a heap by
  iterated swapping of the defect with its parent, until the heap property
  is restored.
\<close>

definition "swap i j h \<equiv> h[i:=h!j, j:=h!i]"

(* Required for termination proof of sift_up *)
lemma parent_less[simp]: "i\<noteq>0 \<Longrightarrow> parent i < i"
  by (auto simp: parent_def)

fun sift_up where
  "sift_up h 0 = h"
| "sift_up h i = (
    if h!i \<ge> h!parent i then h
    else sift_up (swap i (parent i) h) (parent i))"


text \<open>Show that @{const sift_up} restores the heap
  and preserves the multiset of elements in the heap\<close>

lemma sift_up_restore_heap:
  "is_heap_except j h \<Longrightarrow> j<length h \<Longrightarrow> is_heap (sift_up h j)"
  sorry


lemma sift_up_mset: "j<length h \<Longrightarrow> mset (sift_up h j) = mset h"
  sorry

text \<open>For \textbf{3 bonus points}, add an empty, insert, and get-min
  function to the heap implementation, and prove their essential properties.
\<close>

definition emp :: "'a::linorder list" where "emp \<equiv> undefined"
definition get_min :: "'a::linorder list \<Rightarrow> 'a" where "get_min h \<equiv> undefined"
definition ins :: "'a::linorder \<Rightarrow> 'a list \<Rightarrow> 'a list" where "ins x h = undefined"

lemma invar_empty: "is_heap emp" sorry

lemma mset_empty: "mset emp = {#}" sorry

lemma mset_get_min: "is_heap h \<Longrightarrow> mset h \<noteq> {#} \<Longrightarrow> get_min h = Min_mset (mset h)" sorry

lemma invar_ins: "is_heap h \<Longrightarrow> is_heap (ins x h)" sorry

lemma mset_ins: "mset (ins x h) = mset h + {#x#}" sorry


(*<*)
end
(*>*)
