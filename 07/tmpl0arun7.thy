(*<*)
theory tmpl0arun7
  imports Main "HOL-Data_Structures.Sorting"
begin
(*>*)

hide_const (open) inv (*inv is used as a constant in isabelle, renaming it pretty prints the const 
with the long name if the const is not hidden*)

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
  "inv' n [] \<longleftrightarrow> True"|
  "inv' n ((a,b)#ivs) \<longleftrightarrow> n\<le>a \<and> a\<le>b \<and> inv' (b+2) ivs"

definition inv where "inv = inv' 0"



text {* To relate intervals back to sets define an \emph{abstraction function}*}

fun set_of :: "intervals => nat set"
where
  "set_of [] = {}"|
  "set_of ((a,b)#ivs) = {a..b} \<union> set_of ivs"
(*{a..<b} for non inclusive bound*)

text \<open>Define a function to add a single element to the interval list,
  and show its correctness\<close>

fun merge_aux where
  "merge_aux a b [] = [(a,b)]"|
  "merge_aux a b ((c,d)#ivs) = (if b+1 = c then (a,d)#ivs else (a,b)#(c,d)#ivs)"

fun add :: "nat \<Rightarrow> intervals \<Rightarrow> intervals"
  where
  "add i [] = [(i,i)]"|
(*i can be less than a, a-1, between a and b, b+1, greater than b. if b+1 might need to merge with next element too*)
  "add i ((a,b)#ivs) = (
    if i+1 < a then (i,i)#(a,b)#ivs
    else if i+1 = a then (i,b)#ivs
    else if i\<le>b then (a,b)#ivs
    else if i = b+1 then merge_aux a i ivs
    else (a,b)#add i ivs
)"

(* the (a,b)#add i ivs uses ivs which might cause infinite case splits on ivs when originally 
the case split on ivs is done in the add function itself, therefore we write a different function for 
the case splitting
 else if i = b+1 then case ivs of 
      [] \<Rightarrow> [(a,i)]|
      (c,d)#ivs' \<Rightarrow> if i+1 = c then (a,d)#ivs' else (a,i)#ivs*)

lemma add_pres_inv': "n\<le>x \<Longrightarrow> inv' n itl \<Longrightarrow> inv' n (add x itl)"
  apply(induction itl arbitrary: n) (*arbitrary n as the value of n changes in the inv' function definition*)
   apply simp (*simp here keeps induction step as (add x (a #itl)) instead of (a,b) *)
  apply auto (*after this sledgehammer can solve this, auto case splits on products not on anything else,
              hence we need to case split on merge_aux*)
  apply (case_tac itl) (*case split by apply (case_tac itl) but it is unstable so don't use except to verify*)
  apply auto
  done

lemma add_pres_inv: "n\<le>x \<Longrightarrow> inv' n itl \<Longrightarrow> inv' n (add x itl)"
proof (induction itl arbitrary:n)
  case Nil
  then show ?case by auto
next
  case (Cons a itl)
  then show ?case
    apply (cases a)
    apply (cases itl)
    apply auto
    done
qed
  
lemma set_of_add:
  assumes "n\<le>x"
  assumes "inv' n itl"
  shows "set_of (add x itl) = {x} \<union> set_of itl"
  using assms
proof (induction itl arbitrary:n)
case Nil
  then show ?case by auto
next
  case (Cons a itl)
  then show ?case 
    apply (cases a)
    apply (cases itl)
     apply (auto split: if_splits)  (*the apply auto without splitting on ifs shows 10 subcases where it shows all
                                      the if cases in each subcase split: if_splits/if_split_asm where asm is 
                                      assumptions*)
    done
qed
(*not in ex but done in class*)
consts
  a :: "nat"
  b :: "nat set"
  c :: "nat set"

lemma A: "{a} \<union> b = c" sorry

lemma B: "{a} \<union> b \<union> d = c \<union> d"
  using A apply simp (*doing apply (simp add: A) will simplify it to insert a (b \<union> d) = c \<union> d *)
  done
(*not in ex*)
lemma add_correct:
  assumes "inv itl"
  shows "inv (add x itl)" "set_of (add x itl) = insert x (set_of itl)"
  using add_pres_inv' assms tmpl0arun7.inv_def apply fastforce
  using assms set_of_add tmpl0arun7.inv_def by fastforce

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

declare msort2.simps [simp del]

lemma "n = length xs \<Longrightarrow> msort2 n xs = msort xs"
proof (induction n xs rule:msort2.induct)
  case (1 n xs)
  then show ?case 
    apply (auto simp: msort.simps[of xs] msort2.simps[of _ xs]) (*simplifier works innermost to out and  using
                                                                  substitutes instead*)
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
