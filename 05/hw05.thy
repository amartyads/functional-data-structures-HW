theory hw05
  imports
    Complex_Main
    "HOL-Library.Tree"
begin

value "(0::nat) div 0"

lemma
  assumes "n\<ge>0"
  shows "\<exists>ys zs. length ys = length xs div n \<and> xs=ys@zs"
proof (intro exI)
  let ?n = "length xs div n"
  let ?ys = "take ?n xs"
  let ?zs = "drop ?n xs"
  show "length ?ys = length xs div n \<and> xs = ?ys @ ?zs"  by(simp add:min.absorb2)
qed


fun a :: "nat \<Rightarrow> int" where
  "a 0 = 0"
| "a (Suc n) = a n ^ 2 + 1"

thm power_mono[where n = 2]

find_theorems "(_-_)^2"
find_theorems "(_ + _) > _"

lemma "a n \<le> 2 ^ (2 ^ n) - 1"
proof(induction n)
  case 0 thus ?case by simp
next
  case (Suc n)
  assume IH: "a n \<le> 2 ^ 2 ^ n - 1"
    -- \<open>Refer to the induction hypothesis by name \<open>IH\<close> or \<open>Suc.IH\<close>\<close>
  show "a (Suc n) \<le> 2 ^ 2 ^ Suc n - 1"
  proof -
    from IH have azer:"0 \<le> a n" by (smt a.elims power2_less_eq_zero_iff zero_eq_power2)
   
    from IH  have "a (Suc n) = (a n)^2 +1" by simp
    also have "(a n)^2 \<le> (2 ^ 2 ^ n - 1) ^ 2" using power_mono[where n = 2] IH azer by blast
    also have "... \<le> (2 ^ 2 ^ (n + 1)) + 1 - 2*2^(2^(n))" by (simp add: power2_diff power_even_eq)
    also have "... \<le> 2 ^ 2 ^ Suc n - 2 " by (smt Suc.IH Suc_eq_plus1 a.elims power.simps(1) power2_less_eq_zero_iff power_one_right zero_eq_power2)
    finally show ?thesis by auto
    
  qed
qed

end