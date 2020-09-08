(*<*)
theory hw08tmpl
  imports Complex_Main "HOL-Library.Tree"
begin
(*>*)

text {* \NumHomework{Bounding Fibonacci}{June 8}

  We start by defining the Fibonacci sequence, and an alternative
  induction scheme for indexes greater 0:
*}

fun fib :: "nat \<Rightarrow> nat"
  where
    fib0: "fib 0 = 0"
  | fib1: "fib (Suc 0) = 1"
  | fib2: "fib (Suc (Suc n)) = fib (Suc n) + fib n"

lemma f_alt_induct [consumes 1, case_names 1 2 rec]:
  assumes "n > 0"
      and "P (Suc 0)" "P 2" "\<And>n. n > 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n) \<Longrightarrow> P (Suc (Suc n))"
  shows   "P n"
  using assms(1)
proof (induction n rule: fib.induct)
  case (3 n)
  thus ?case using assms by (cases n) (auto simp: eval_nat_numeral)
qed (auto simp: \<open>P (Suc 0)\<close> \<open>P 2\<close>)

text \<open>Show that the Fibonacci numbers grow exponentially, i.e., that they are
  bounded from below by \<open>1.5\<^sup>n/3\<close>.

  Use the alternative induction scheme defined above.
\<close>
lemma fib_lowerbound: "n > 0 \<Longrightarrow> real (fib n) \<ge> 1.5 ^ n / 3"
proof (induction n rule: f_alt_induct)
oops

text \<open>
  \NumHomework{AVL Trees}{June 8}

  AVL trees are binary search trees where, for each node, the heights of
  its subtrees differ by at most one. In this homework, you are to bound
  the minimal number of nodes in an AVL tree of a given height.

  First, define the AVL invariant on binary trees.
  Note: In practice, one additionally stores the heights or height difference
  in the nodes, but this is not required for this exercise.
\<close>


fun avl :: "'a tree \<Rightarrow> bool"
where
"avl _ = undefined"


text \<open>Show that an AVL tree of height \<open>h\<close> has at least \<open>fib (h+2)\<close> nodes:\<close>
lemma avl_fib_bound: "avl t \<Longrightarrow> height t = h \<Longrightarrow> fib (h+2) \<le> size1 t"
  oops

text \<open>Combine your results to get an exponential lower bound on the number
  of nodes in an AVL tree.\<close>
lemma avl_lowerbound:
  assumes "avl t"
  shows "1.5 ^ (height t + 2) / 3 \<le> real (size1 t)"
  oops


(*<*)
end
(*>*)
