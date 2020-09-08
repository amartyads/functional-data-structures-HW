theory hw06
  imports Main 
begin

fun funky::"int \<Rightarrow> int" where
 "funky k = (k - 3)^2"

value "sort_key funky [(2::int), 1, 3, 4]"

find_theorems "insort_key"

lemma "[x\<leftarrow>sort_key k xs. k x = a] = [x\<leftarrow>xs. k x = a]"
  apply(induction xs)
   apply(auto simp: filter_insort_triv filter_insort insort_is_Cons)
  done

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

lemma aux1[simp]: "(\<forall>x\<in>set xs. x < p) \<Longrightarrow> (\<forall>y\<in>set ys. \<not> y < p) \<Longrightarrow> (a < p) \<Longrightarrow> insort a (xs@ys) = (insort a xs) @ ys"
  apply(induction xs)
  apply(induction ys)
  by auto

lemma aux2[simp]: "(\<forall>x\<in>set xs. x < p) \<Longrightarrow> (\<forall>y\<in>set ys. \<not> y < p) \<Longrightarrow> \<not>(a < p) \<Longrightarrow> insort a (xs@ys) = (xs) @ insort a ys"
  apply(induction xs)
  apply(induction ys)
  by auto


lemma partition_correct[simp]: "sort xs = sort [x\<leftarrow>xs. x<p] @ sort [x\<leftarrow>xs. \<not>(x<p)]"
  apply(induction xs)
  apply(simp)
   apply(clarsimp)
  apply(smt aux1 aux2 filter_set member_filter set_sort)
  done

lemma "k<length xs \<Longrightarrow> quickselect xs k = sort xs ! k"
proof (induction xs k rule: quickselect.induct)
  print_cases
  case (1 x xs k)
  note IH = "1.IH"[OF refl refl]

  let ?xs1 = "[y\<leftarrow>xs. y<x]"
  

  show ?case proof cases
    assume "k<length ?xs1" then show ?thesis apply (simp add: IH) sorry
  next
    assume "\<not>(k<length ?xs1)" then show ?thesis sorry
        
  qed
next
  case 2 then show ?case by simp
qed


end