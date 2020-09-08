theory ex01
  imports Main
begin

term "op+"

lemma "a + b = b + (a :: nat)"
  by auto

lemma "a + (b + c) = (a + b) + (c::nat)"
  by auto

term "Nil"
term "Cons a b"

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0"
| "count (x#xs) y = (if x=y then count xs y + 1 else count xs y)"

fun count' :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count' [] _ = 0"
| "count' (x # xs) y = (if x = y then 1 else 0) + count' xs y"

value "count [1,2,3,4,2,2,2::int] 2"

find_theorems "length [] = _"
find_theorems "length (_ # _) =  _"

lemma "count xs a \<le> length xs"
  apply(induction xs)
   apply(simp)
  apply(simp)
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] y = [y]"
| "snoc (x # xs) y = x # snoc xs y"

lemma "snoc xs x = xs@[x]"
  apply(induction xs) by auto

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = snoc (reverse xs) x"

lemma aux: "reverse (snoc xs x) = x # reverse xs"
  apply(induction xs) by auto

lemma rev_rev[simp]: "reverse (reverse xs) = xs"
  apply (induction xs)
   apply (auto simp:aux)
  done

lemma "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto simp:)
  apply(subst aux)
  apply auto
  done


  
end