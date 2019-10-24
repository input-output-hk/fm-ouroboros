section \<open>Transition Systems of the \<open>\<natural>\<close>-calculus\<close>

theory Natural_Transition_Systems
  imports Transition_Systems.Transition_Systems Processes
begin

(* FIXME:
  Every occurrence of “preservation” in this theory (including in comments) should be replaced by
  “compatibility” later.
*)

locale natural_transition_system =
  transition_system lift transition
    for lift :: "([process, process] \<Rightarrow> bool) \<Rightarrow> (['residual, 'residual] \<Rightarrow> bool)" and transition +
  assumes receive_preservation:
    "\<And>a P Q. (\<And>x. P x \<sim> Q x) \<Longrightarrow> a \<triangleright> x. P x \<sim> a \<triangleright> x. Q x"
  assumes parallel_preservation:
    "\<And>p\<^sub>1 p\<^sub>2 q\<^sub>1 q\<^sub>2. \<lbrakk>p\<^sub>1 \<sim> p\<^sub>2; q\<^sub>1 \<sim>q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<sim> p\<^sub>2 \<parallel> q\<^sub>2"
  assumes new_channel_preservation:
    "\<And>P Q. (\<And>a. P a \<sim> Q a) \<Longrightarrow> \<nu> a. P a \<sim> \<nu> a. Q a"
begin

lemma guard_preservation:
  assumes "p \<sim> q"
  shows "\<phi> ? p \<sim> \<phi> ? q"
  using assms by simp

lemma general_parallel_preservation:
  assumes "\<And>x. f x \<sim> g x"
  shows "general_parallel f xs \<sim> general_parallel g xs"
  using assms and parallel_preservation
  by (induction xs) simp_all

end

end
