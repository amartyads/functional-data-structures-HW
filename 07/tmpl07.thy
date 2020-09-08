(*<*)
theory tmpl07
  imports Main "HOL-Data_Structures.Sorting"
begin
(*>*)


text {* \ExerciseSheet{7}{25.~5.~2018} *}


text {* \Exercise{Interval Lists}

 Sets of natural numbers can be implemented as lists of intervals, where
an interval is simply a pair of numbers.  For example the set @{term "{2, 3, 5,
7, 8, 9::nat}"} can be represented by the list @{term "[(2, 3), (5, 5),
(7::nat, 9::nat)]"}.  A typical application is the list of free blocks of
dynamically allocated memory. *}

text {* We introduce the type *}

type_synonym intervals = "(nat*nat) list"

text {* Next, define an \emph{invariant}
that characterizes valid interval lists:
For efficiency reasons intervals should be sorted in ascending order, the lower
bound of each interval should be less than or equal to the upper bound, and the
intervals should be chosen as large as possible, i.e.\ no two adjacent
intervals should overlap or even touch each other.  It turns out to be
convenient to define @{term inv} in terms of a more general function
such that the additional argument is a lower bound for the intervals in
the list:*}

fun inv' :: "nat \<Rightarrow> intervals \<Rightarrow> bool" where
  "inv' _ _ \<longleftrightarrow> undefined"

definition inv where "inv = inv' 0"



text {* To relate intervals back to sets define an \emph{abstraction function}*}

fun set_of :: "intervals => nat set"
where
  "set_of _ = undefined"

text \<open>Define a function to add a single element to the interval list,
  and show its correctness\<close>


fun add :: "nat \<Rightarrow> intervals \<Rightarrow> intervals"
  where
  "add _ _ = undefined"

lemma add_correct:
  assumes "inv is"
  shows "inv (add x is)" "set_of (add x is) = insert x (set_of is)"
  oops

text \<open>Hints:
  \<^item> Sketch the different cases (position of element relative to the first interval of the list)
    on paper first
  \<^item> In one case, you will also need information about the second interval of the list.
    Do this case split via an auxiliary function! Otherwise, you may end up with a recursion equation of the form
      \<open>f (x#xs) = \<dots> case xs of x'#xs' \<Rightarrow> \<dots> f (x'#xs') \<dots>\<close>
    combined with \<open>split: list.splits\<close> this will make the simplifier loop!

\<close>


text \<open>\Exercise{Optimized Mergesort}

  Import @{theory "Sorting"} for this exercise.
  The @{const msort} function recomputes the length of the list in each iteration.
  Implement an optimized version that has an additional parameter keeping track
  of the length, and show that it is equal to the original @{const msort}.
\<close>

(* Optimized mergesort *)

fun msort2 :: "nat \<Rightarrow> 'a::linorder list \<Rightarrow> 'a list"
  where "msort2 _ _ = undefined"

lemma "n = length xs \<Longrightarrow> msort2 n xs = msort xs"
  oops

text \<open>Hint:
  Use @{thm [source] msort.simps} only when instantiated to a particular \<open>xs\<close>
  (@{thm [source] msort.simps[of xs]}),
  otherwise the simplifier will loop!
\<close>



text \<open> \NumHomework{Deletion from Interval Lists}{June 1}

  Implement and prove correct a delete function.

  Hints:
    \<^item> The correctness lemma is analogous to the one for add.
    \<^item> A monotonicity property on \<open>inv'\<close> may be useful, i.e.,
      @{prop \<open>inv' m is \<Longrightarrow> inv' m' is\<close>} if @{prop \<open>m'\<le>m\<close>}
    \<^item> A bounding lemma, relating \<open>m\<close> and the elements of @{term \<open>set_of is\<close>}
      if @{prop \<open>inv' m is\<close>}, may be useful.
\<close>



fun del :: "nat \<Rightarrow> intervals \<Rightarrow> intervals"
where
  "del _ _ = undefined"

lemma del_correct: "Come up with a meaningful spec yourself" oops



text \<open> \NumHomework{Addition of Interval to Interval List}{June 1}
  For 3 \<^bold>\<open>bonus points\<close>, implement and prove correct a function
  to add a whole interval to an interval list. The runtime must
  not depend on the size of the interval, e.g., iterating over the
  interval and adding the elements separately is not allowed!
\<close>

fun addi :: "nat \<Rightarrow> nat \<Rightarrow> intervals \<Rightarrow> intervals"
where
  "addi i j is = undefined"

lemma addi_correct:
  assumes "inv is" "i\<le>j"
  shows "inv (addi i j is)" "set_of (addi i j is) = {i..j} \<union> (set_of is)"
  sorry


(*<*)
end
(*>*)
