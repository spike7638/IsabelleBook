theory Roland
  imports Complex_Main
begin   

lemma induction_from_start:
  fixes P:: "nat \<Rightarrow> bool"
  fixes s::"nat"
  assumes "P s"
  assumes "\<And>n. n \<ge> s \<Longrightarrow> P (n) \<Longrightarrow> P (Suc n)"
  shows "\<And>n. n \<ge> s  \<Longrightarrow> P n"

thm nat_induct_at_least

proof -
  let Q n = "P (s + n)"
  show "\<And>n. Q(n)" 

  using assms by (metis dec_induct diff_Suc_1 le_imp_less_Suc)

lemma box_le: "a \<le> b \<Longrightarrow> a = c \<Longrightarrow> b = d \<Longrightarrow> c \<le> d" by fast

theorem fac_outgrows_powers_of_two:
  fixes n :: nat
  assumes "n \<ge> 4"
  shows "2 ^ n \<le> fac n"
proof (induction n)
  case 4
  then show ?case sorry
next
  case (Suc n)
  then show ?case sorry
qed

proof (rule assms [THEN [3] induction_from_start])
  fix n :: nat
  assume "n = 4"
  thus "2 ^ n \<le> fac n" 
    unfolding fac_def by simp
next
  fix n :: nat
  assume "n > 4"
  hence "n > 0" by fastforce
  assume "2 ^ (n - 1) \<le> fac (n - 1)"
  hence "2 * 2 ^ (n - 1) \<le> n * fac (n - 1)"
    using \<open>n > 4\<close> by (simp add: mult_le_mono)
  moreover have "2 * 2 ^ (n - 1) = 2 ^ n"
    using \<open>n > 0\<close> by (simp add: power_eq_if)
  moreover have "n * fac (n - 1) = fac n"
    using \<open>n > 0\<close> by (metis One_nat_def Suc_pred fac.simps(2))
  ultimately show "2 ^ n \<le> fac n" by (rule box_le)
qed
