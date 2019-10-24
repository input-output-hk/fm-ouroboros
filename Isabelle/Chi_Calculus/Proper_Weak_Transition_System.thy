section \<open>Proper Weak Transition System\<close>

theory Proper_Weak_Transition_System
  imports Basic_Weak_Transition_System Proper_Transition_System
begin

inductive proper_silent :: "['p, 'p proper_residual] \<Rightarrow> bool" where
  proper_internal_is_silent: "proper_silent p (\<lparr>\<tau>\<rparr> p)"

interpretation proper: std_weak_residual proper_lift proper_silent
proof
  show "proper_silent OO proper_silent\<inverse>\<inverse> = (=)"
    by (blast elim: proper_silent.cases intro: proper_silent.intros)
next
  show "proper_silent\<inverse>\<inverse> OO proper_silent \<le> (=)"
    by (blast elim: proper_silent.cases)
next
  fix \<X>
  show "\<X> OO proper_silent = proper_silent OO proper_lift \<X>"
  proof (intro ext, intro iffI)
    fix p and c
    assume "(\<X> OO proper_silent) p c"
    then show "(proper_silent OO proper_lift \<X>) p c"
      by (blast elim: proper_silent.cases intro: proper_silent.intros simple_lift)
  next
    fix p and c
    assume "(proper_silent OO proper_lift \<X>) p c"
    then show "(\<X> OO proper_silent) p c"
      by (blast elim: proper_silent.cases proper_lift_cases intro: proper_silent.intros)
  qed
qed

interpretation proper: weak_transition_system proper_silent proper.absorb proper_transition
  by intro_locales

notation proper.weak_transition (infix "\<Rightarrow>\<^sub>\<sharp>" 50)
notation proper.weak.pre_bisimilarity (infix "\<lessapprox>\<^sub>\<sharp>" 50)
notation proper.weak.bisimilarity (infix "\<approx>\<^sub>\<sharp>" 50)

(* NOTE:
  This will become obsolete once there is only one locale interpretation for the strong transition
  system.
*)
lemma proper_strong_bisimilarity_in_weak_bisimilarity [equivalence]: "(\<sim>\<^sub>\<sharp>) \<le> (\<approx>\<^sub>\<sharp>)"
  sorry

lemma basic_weak_bisimilarity_in_proper_weak_bisimilarity [equivalence]: "(\<approx>\<^sub>\<flat>) \<le> (\<approx>\<^sub>\<sharp>)"
  sorry

lemma basic_strong_bisimilarity_in_proper_weak_bisimilarity [equivalence]: "(\<sim>\<^sub>\<flat>) \<le> (\<approx>\<^sub>\<sharp>)"
proof -
  have "(\<sim>\<^sub>\<flat>) \<le> (\<sim>\<^sub>\<sharp>)" using basic_bisimilarity_in_proper_bisimilarity .
  also have "\<dots> \<le> (\<approx>\<^sub>\<sharp>)" using proper_strong_bisimilarity_in_weak_bisimilarity .
  finally show ?thesis .
qed

lemma proper_weak_receive_preservation: "(\<And>x. P x \<approx>\<^sub>\<sharp> Q x) \<Longrightarrow> a \<triangleright> x. P x \<approx>\<^sub>\<sharp> a \<triangleright> x. Q x"
  sorry

lemma proper_weak_parallel_preservation_left: "p\<^sub>1 \<approx>\<^sub>\<sharp> p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<parallel> q \<approx>\<^sub>\<sharp> p\<^sub>2 \<parallel> q"
  sorry

lemma proper_weak_parallel_preservation_right: "q\<^sub>1 \<approx>\<^sub>\<sharp> q\<^sub>2 \<Longrightarrow> p \<parallel> q\<^sub>1 \<approx>\<^sub>\<sharp> p \<parallel> q\<^sub>2"
  sorry

lemma proper_weak_parallel_preservation: "\<lbrakk>p\<^sub>1 \<approx>\<^sub>\<sharp> p\<^sub>2; q\<^sub>1 \<approx>\<^sub>\<sharp> q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<approx>\<^sub>\<sharp> p\<^sub>2 \<parallel> q\<^sub>2"
  sorry

lemma proper_weak_new_channel_preservation: "(\<And>a. P a \<approx>\<^sub>\<sharp> Q a) \<Longrightarrow> \<nu> a. P a \<approx>\<^sub>\<sharp> \<nu> a. Q a"
  sorry

quotient_type proper_weak_behavior = process / "(\<approx>\<^sub>\<sharp>)"
  using proper.weak.bisimilarity_is_equivalence .

declare proper_weak_behavior.abs_eq_iff [equivalence_transfer]

(* FIXME:
  Once #14 is resolved, the following should be done based on \<open>natural_transition_system\<close>, like in
  the strong case.
*)
context begin

private
  lift_definition stop' :: proper_weak_behavior
  is Stop .

private
  lift_definition send' :: "[chan, val] \<Rightarrow> proper_weak_behavior"
  is Send .

private
  lift_definition receive' :: "[chan, val \<Rightarrow> proper_weak_behavior] \<Rightarrow> proper_weak_behavior"
  is Receive
  using proper_weak_receive_preservation .

private
  lift_definition parallel' :: "[proper_weak_behavior, proper_weak_behavior] \<Rightarrow> proper_weak_behavior"
  is Parallel
  using proper_weak_parallel_preservation .

private
  lift_definition new_channel' :: "(chan \<Rightarrow> proper_weak_behavior) \<Rightarrow> proper_weak_behavior"
  is NewChannel
  using proper_weak_new_channel_preservation .

private
  lift_definition guard' :: "[bool, proper_weak_behavior] \<Rightarrow> proper_weak_behavior"
  is guard
  sorry

private
  lift_definition general_parallel' :: "['a \<Rightarrow> proper_weak_behavior, 'a list] \<Rightarrow> proper_weak_behavior"
  is general_parallel
  sorry

lemmas [equivalence_transfer] =
  stop'.abs_eq
  send'.abs_eq
  receive'.abs_eq
  parallel'.abs_eq
  new_channel'.abs_eq
  guard'.abs_eq
  general_parallel'.abs_eq

end

end
