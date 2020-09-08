theory UFDS
  imports Main
begin
fun fpow where
  "fpow f 0 = id"
| "fpow f (Suc n) = f o fpow f n"

lemma fpow_is_compow[simp]: "fpow = op ^^"
proof (intro ext)
  fix f n x
  show "fpow f n x = (f^^n) x"
    apply (induction n arbitrary: x)
     apply auto
    done
qed



(*location of array contains parent*)

partial_function (tailrec) find' where
  "find' ls i = (if ls!i = i then i else find' ls (ls!i))"

thm find'.simps


definition "init n = [0..<n]"
definition "pred ls i = ls!i"
definition "is_root ls i \<longleftrightarrow> pred ls i = i"
(*definition find where "find ls i == fpow (pred ls) (length ls) i"*)
definition "invar ls \<longleftrightarrow> 
  (set ls \<subseteq> {0..<length ls}) 
\<and> (\<forall>i<length ls. \<exists>n\<in>{0..<length ls}. is_root ls (fpow (pred ls) n i)) "


definition union where "union i j ls = ls[find' ls i := find' ls j]"

type_synonym eqcs = "nat \<Rightarrow> nat set"

definition \<alpha> :: "nat list \<Rightarrow> eqcs" where "\<alpha> ls i = 
  (if i<length ls then {j. j<length ls \<and> find' ls j = find' ls i} else {i})"

definition union_eqc :: "nat \<Rightarrow> nat \<Rightarrow> eqcs \<Rightarrow> eqcs"
  where
  "union_eqc x y eqc i = (if i \<in> eqc x \<union> eqc y then eqc x \<union> eqc y else eqc i)"

value "([5,1,2]::nat list)[1:=2]"

lemma 
  assumes "invar ls" "x<length ls" "y<length ls"
  shows "length ls = length (union x y ls)"
  using assms
proof(induction ls arbitrary: x y)
  case Nil
  then show ?case by auto
next
  case (Cons a ls)
  then show ?case 
    unfolding union_def
    by (metis length_list_update)
qed

lemma 
  assumes "invar ls" "x<length ls" "y<length ls"
  shows "invar (union x y ls)"
  apply(auto simp:invar_def)
  
  oops


lemma 
  assumes "invar ls" "x<length ls" "y<length ls"
  shows "\<alpha> (union x y ls) = union_eqc x y (\<alpha> ls)"


lemma "invar [0..<N]"
proof(induction N)
    case 0
    then show ?case
      unfolding invar_def
      by(auto)
  next
    case (Suc N)
    then show ?case
      
      unfolding invar_def
      apply(auto)
      have "n = N \<or> n \<in> {0..<N}" (is "?C1 \<or> ?C2")
      
      qed

  thm find'.simps

lemma "\<alpha> [0..<N] i = {i}"
  apply (auto simp add: \<alpha>_def)
  apply (auto simp add: \<alpha>_def find'.simps split del: if_split)

  apply (subst (asm) find'.simps)
  apply (subst (asm) (2) find'.simps)
  apply auto
  done

lemma "find "


fun natbelow :: "nat \<Rightarrow> nat list" where
  "natbelow 0 = [0]"
| "natbelow (Suc n) = (Suc n) # natbelow n"

value "rev [1::nat,2,3]"

fun init :: "nat \<Rightarrow> nat list" where
 "init n = rev (natbelow n)"

value "init 10"
value "[0..<10]"

term upto
term upt

fun findParentAux :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "findParentAux n 0 xs  = (xs!n)"
| "findParentAux n (Suc b) xs = (if (xs!n = n) then n else findParentAux (xs!n) b xs)"

fun findParent :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "findParent n xs = findParentAux n (size xs) xs"


fun isSameSet :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "isSameSet a b l = (findParent a l = findParent b l)"

value "init 10"
value "findParent 5 [0, 1, 2, 3, 4, 5, 6]"
value "isSameSet 2 3 [0, 1, 4, 5, 5, 1]"

fun replace :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "replace _ _ [] = []"
| "replace a b (x#xs) = (if (a = x) then b#xs else x#(replace a b xs))"

value "let ls = [0::nat,1,2,3,4,5,6] in ls[4:=9]"


fun union :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "union a b ls = (if (isSameSet a b ls) then ls else (replace (findParent a ls) b ls))"

value "isSameSet 2 3 (union 5 3 [0, 1, 2, 3, 4, 2, 6])"
value "union 5 0 [0, 1, 2, 3, 4, 2, 6]"
value "union 1 0 [1, 0]"

fun valid :: "nat list \<Rightarrow> bool" where
  "valid [] = False"
| "valid t = (\<forall>x \<in> set t. t!x = x)"

value "valid [1, 0]"
value "init 10"
value "valid (init 10)"

fun sizeufd :: "nat list \<Rightarrow> nat" where
  "sizeufd fn = size fn + 1"

(* here be dragons *)

lemma isSameSetWorks:"\<not> isSameSet a b t \<Longrightarrow> findParent a t \<noteq> findParent b t"
  by simp

lemma unionWorks:"valid t \<Longrightarrow> n \<ge> max a b \<Longrightarrow> isSameSet a b (union a b (init n))"
  apply(auto)

end