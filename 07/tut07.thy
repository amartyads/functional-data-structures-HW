(*<*)
theory tut07
  imports Main "HOL-Data_Structures.Sorting"
begin
(*>*)

hide_const (open) inv


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
  "inv' n [] \<longleftrightarrow> True"
| "inv' n ((a,b)#ivs) \<longleftrightarrow> n\<le>a \<and> a\<le>b \<and> inv' (b+2) ivs"

definition inv where "inv = inv' 0"



text {* To relate intervals back to sets define an \emph{abstraction function}*}

fun set_of :: "intervals => nat set"
where
  "set_of [] = {}"
| "set_of ((a,b)#ivs) = {a..b} \<union> set_of ivs"

text \<open>Define a function to add a single element to the interval list,
  and show its correctness\<close>


fun merge_aux where
  "merge_aux a b [] = [(a,b)]"
| "merge_aux a b ((c,d)#ivs) = (if b+1=c then (a,d)#ivs else (a,b)#(c,d)#ivs)"

fun add :: "nat \<Rightarrow> intervals \<Rightarrow> intervals"
  where
  "add i [] = [(i,i)]"
| "add i ((a,b)#ivs) = (
    if i+1 < a then (i,i)#(a,b)#ivs
    else if i+1 = a then (i,b)#ivs
    else if i\<le>b then (a,b)#ivs
    else if i=b+1 then merge_aux a i ivs
    else (a,b)#add i ivs
  )"


lemma add_pres_inv:
  "n\<le>x \<Longrightarrow> inv' n ivs \<Longrightarrow> inv' n (add x ivs)"
proof (induction ivs arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a ivs)
  then show ?case
    apply (cases a)
    apply (cases ivs)
    apply auto
    done
qed

lemma set_of_add:
  assumes "n\<le>x"
  assumes "inv' n ivs"
  shows "set_of (add x ivs) = {x} \<union> set_of ivs"
  using assms
proof (induction ivs arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a ivs)
  then show ?case
    apply (cases a)
    apply (cases ivs)
    apply (auto split: if_splits)
    done
qed


lemma add_correct:
  assumes "inv is"
  shows "inv (add x is)" "set_of (add x is) = {x} \<union> set_of is"
  using add_pres_inv assms tut07.inv_def apply fastforce
  using assms set_of_add tut07.inv_def by fastforce


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

fun msort2 :: "nat \<Rightarrow> 'a::linorder list \<Rightarrow> 'a list" where
"msort2 n xs = (
  if n \<le> 1 then xs
  else merge (msort2 (n div 2) (take (n div 2) xs)) (msort2 (n - n div 2) (drop (n div 2) xs)))"

declare msort2.simps[simp del]

lemma "n = length xs \<Longrightarrow> msort2 n xs = msort xs"
proof (induction n xs rule: msort2.induct)
  case (1 n xs)
  then show ?case
    using msort.simps[of xs] msort2.simps[of n xs]
    apply (auto simp: )
    done

qed


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
