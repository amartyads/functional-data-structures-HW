(*<*)
theory tmpl06
  imports Main
begin
(*>*)


text {* \ExerciseSheet{6}{18.~5.~2018} *}

text \<open>\Exercise{Complexity of Naive Reverse}
  Show that the naive reverse function needs quadratically many
  \<open>Cons\<close> operations in the length of the input list.
  (Note that \<open>[x]\<close> is syntax sugar for \<open>Cons x []\<close>!)
\<close>

thm append.simps

fun reverse where
  "reverse [] = []"
| "reverse (x#xs) = reverse xs @ [x]"

(** Define cost functions and prove that they are equal to quadratic function *)

text \<open>
  \Exercise{Simple Paths}
  Recall the definition of paths from last exercise sheet:
\<close>
fun path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where
  "path G u [] v \<longleftrightarrow> u=v"
| "path G u (x#xs) v \<longleftrightarrow> G u x \<and> path G x xs v"

lemma path_append[simp]: "path G u (p1@p2) v \<longleftrightarrow> (\<exists>w. path G u p1 w \<and> path G w p2 v)"
  by (induction p1 arbitrary: u) auto


text \<open>
  A simple path is a path without loops, or, in other words, a path
  where no node occurs twice. (Note that the first node of the path is
  not included, such that there may be a simple path from \<open>u\<close> to \<open>u\<close>.)

  Show that for every path, there is a corresponding simple path.

  Hint: Induction on the length of the path
\<close>
thm measure_induct_rule[where f=length, case_names shorter]

thm not_distinct_decomp

lemma exists_simple_path:
  assumes "path G u p v"
  shows "\<exists>p'. path G u p' v \<and> distinct p'"
  oops


text \<open>\NumHomework{Stability of Insertion Sort}{May 25}
  Have a look at Isabelle's standard implementation of sorting: @{const sort_key}.
  (Use Ctrl-Click to jump to the definition in @{file "~~/src/HOL/List.thy"})
  Show that this function is a stable sorting algorithm, i.e., the order of elements
  with the same key is not changed during sorting!
\<close>

lemma "[x\<leftarrow>sort_key k xs. k x = a] = [x\<leftarrow>xs. k x = a]"
  oops

term "[x\<leftarrow>xs. P x]"
text \<open>
  Note: @{term [source] \<open>[x\<leftarrow>xs. P x] \<close>} is syntax sugar for @{term [source] \<open>filter P xs\<close>},
  where the filter function returns only the elements of list \<open>xs\<close> for which \<open>P xs = True\<close>.

  Hint: You do not necessarily need Isar, and the auxiliary lemmas
    you need are already in Isabelle's library. @{command find_theorems} is your friend!
\<close>


text \<open>\NumHomework{Quickselect}{May 25}

From \<^url>\<open>https://en.wikipedia.org/wiki/Quickselect\<close>:

Quickselect is a selection algorithm to find the kth smallest element in an unordered list.
It is related to the quicksort sorting algorithm.
Like quicksort, it was developed by Tony Hoare, and thus is also known as Hoare's selection
algorithm. Like quicksort, it is efficient in practice and has good average-case performance,
but has poor worst-case performance. Quickselect and its variants are the selection algorithms
most often used in efficient real-world implementations.

Quickselect uses the same overall approach as quicksort, choosing one element as a pivot and
partitioning the data in two based on the pivot, accordingly as less than or greater than the
pivot. However, instead of recursing into both sides, as in quicksort, quickselect only
recurses into one side --- the side with the element it is searching for.


Your task is to prove correct the quickselect algorithm, which can be
  implemented in Isabelle as follows:
\<close>

fun quickselect :: "'a::linorder list \<Rightarrow> nat \<Rightarrow> 'a" where
  "quickselect (x#xs) k = (let
    xs1 = [y\<leftarrow>xs. y<x];
    xs2 = [y\<leftarrow>xs. \<not>(y<x)]
  in
    if k<length xs1 then quickselect xs1 k
    else if k=length xs1 then x
    else quickselect xs2 (k-length xs1-1)
  )"
| "quickselect [] _ = undefined"


text \<open>Your first task is to prove the crucial idea of quicksort, i.e., that
  partitioning wrt.\ a pivot element $p$ is correct.
\<close>

lemma partition_correct: "sort xs = sort [x\<leftarrow>xs. x<p] @ sort [x\<leftarrow>xs. \<not>(x<p)]"
  oops

text \<open>
  Hint: Induction, and auxiliary lemmas to transform a term of the
    form @{term \<open>insort x (xs@ys)\<close>} when you know that \<open>x\<close> is greater than
    all elements in \<open>xs\<close> / less than or equal all elements in \<open>ys\<close>.
\<close>



text \<open>Next, show that quickselect is correct\<close>
lemma "k<length xs \<Longrightarrow> quickselect xs k = sort xs ! k"
  text \<open>Proceed by computation induction, and a case distinction according to the
    cases in the body of the quickselect function\<close>
proof (induction xs k rule: quickselect.induct)
  case (1 x xs k)

  text \<open>Note: To make the induction hypothesis more readable,
    you can collapse the first two premises of the form \<open>?x=\<dots>\<close>
    by reflexivity:\<close>
  note IH = "1.IH"[OF refl refl]

  text \<open>Insert your proof here!\<close>

  show ?case sorry
next
  case 2 then show ?case by simp
qed





(*<*)
end
(*>*)
