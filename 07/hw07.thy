theory hw07
  imports Main
begin

hide_const (open) inv

type_synonym intervals = "(nat*nat) list"

fun inv' :: "nat \<Rightarrow> intervals \<Rightarrow> bool" where
  "inv' n [] \<longleftrightarrow> True"|
  "inv' n ((a,b)#ivs) \<longleftrightarrow> n\<le>a \<and> a\<le>b \<and> inv' (b+2) ivs"

definition inv where "inv = inv' 0"


fun set_of :: "intervals \<Rightarrow> nat set"
where
  "set_of [] = {}"|
  "set_of ((a,b)#ivs) = {a..b} \<union> set_of ivs"


fun del :: "nat \<Rightarrow> intervals \<Rightarrow> intervals"
  where
   "del x [] = []"
|  "del x ((a,b)#lis) = (
    if (x < a) then (a,b)#lis
    else if (x = a \<and> x = b) then lis
    else if (x = a) then ((a+1), b)#lis
    else if (x < b) then (a,x-1)#(x+1,b)#lis
    else if (x = b) then (a,b-1)#lis
    else (a,b)#(del x lis))"

value "del (12::nat) [(2,5),(7,7),(9,11)]"
value "set_of [] - {1::nat}"

lemma del_pres_inv: "n\<le>x \<Longrightarrow> inv' n itl \<Longrightarrow> inv' n (del x itl)"
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

lemma set_of_del:
  assumes "n\<le>x"
  assumes "inv' n itl"
  shows "set_of (del x itl) =  set_of itl - {x}"
  using assms
proof (induction itl arbitrary:n)
case Nil
  then show ?case by auto
next
  case (Cons a itl)
  then show ?case 
    apply (cases a)
    apply (cases itl)
     apply (auto split: if_splits)
    apply (auto)
    done
qed


lemma del_correct:
  assumes "inv itl"
  shows "inv (del x itl)" "set_of (del x itl) =  (set_of itl) - {x}"
  using assms del_pres_inv hw07.inv_def apply fastforce
  using assms hw07.inv_def set_of_del by fastforce









fun addi :: "nat \<Rightarrow> nat \<Rightarrow> intervals \<Rightarrow> intervals"
where
  "addi i j [] = [(i,j)]"|
  "addi i j ((a,b)#lis) = (
    if j + 1 < a then ((i,j)#(a,b)#lis)
    else if j+1 = a then ((i,b)#lis)
    else if j \<le> b then(
      if i < a then ((i,b)#lis)
      else ((a,b)#lis))
    else (
      if i < a then addi i j lis
      else if i \<le> b+1 then addi a j lis
      else ((a,b)#(addi i j lis)))
    )"

value "addi 5 99 [(2,5),(7,7),(9,11)]"

lemma addi_pres_inv: "n\<le>i \<Longrightarrow> i\<le>j \<Longrightarrow> inv' n itl \<Longrightarrow> inv' n (addi i j itl)"
proof (induction i j itl arbitrary:n rule:addi.induct)
  case (1 i j)
  then show ?case by auto
next
  case (2 i j a b itl)
  then show ?case
    apply(cases itl)
     apply(auto)
    done
qed

lemma set_of_addi:
  assumes "n\<le>i" "i\<le>j"
  assumes "inv' n itl"
  shows "set_of (addi i j itl) = {i..j} \<union> set_of itl"
  using assms
proof (induction i j itl arbitrary:n rule:addi.induct)
  case (1 i j)
  then show ?case by auto
next
  case (2 i j a b lis)
  then show ?case
    apply(cases lis)
     apply(cases a)
      apply(cases b)
       apply (auto split:if_splits)
          apply fastforce
         apply fastforce
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
    done
qed

lemma addi_correct:
  assumes "inv is" "i\<le>j"
  shows "inv (addi i j is)" "set_of (addi i j is) = {i..j} \<union> (set_of is)"
  using addi_pres_inv assms hw07.inv_def zero_order(3) apply force
  by (metis assms hw07.inv_def le0 set_of_addi)


end
