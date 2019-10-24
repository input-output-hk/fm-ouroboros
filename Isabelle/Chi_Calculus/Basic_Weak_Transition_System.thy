section \<open>Basic Weak Transition System\<close>

theory Basic_Weak_Transition_System
  imports
    Transition_Systems.Std_Weak_Residuals
    Transition_Systems.Weak_Transition_Systems
    Basic_Transition_System
begin

inductive basic_silent :: "['p, 'p basic_residual] \<Rightarrow> bool" where
  basic_internal_is_silent: "basic_silent p (\<lbrace>\<tau>\<rbrace> p)"

interpretation basic: std_weak_residual basic_lift basic_silent
proof
  show "basic_silent OO basic_silent\<inverse>\<inverse> = (=)"
    by (blast elim: basic_silent.cases intro: basic_silent.intros)
next
  show "basic_silent\<inverse>\<inverse> OO basic_silent \<le> (=)"
    by (blast elim: basic_silent.cases)
next
  fix \<X>
  show "\<X> OO basic_silent = basic_silent OO basic_lift \<X>"
  proof (intro ext, intro iffI)
    fix p and c
    assume "(\<X> OO basic_silent) p c"
    then show "(basic_silent OO basic_lift \<X>) p c"
      by (blast elim: basic_silent.cases intro: basic_silent.intros acting_lift)
  next
    fix p and c
    assume "(basic_silent OO basic_lift \<X>) p c"
    then show "(\<X> OO basic_silent) p c"
      by (blast elim: basic_silent.cases basic_lift_cases intro: basic_silent.intros)
  qed
qed

interpretation basic: weak_transition_system basic_silent basic.absorb basic_transition
  by intro_locales

notation basic.weak_transition (infix "\<Rightarrow>\<^sub>\<flat>" 50)
notation basic.weak.pre_bisimilarity (infix "\<lessapprox>\<^sub>\<flat>" 50)
notation basic.weak.bisimilarity (infix "\<approx>\<^sub>\<flat>" 50)

(* NOTE:
  This will become obsolete once there is only one locale interpretation for the strong transition
  system.
*)
lemma basic_strong_bisimilarity_in_weak_bisimilarity [equivalence]: "(\<sim>\<^sub>\<flat>) \<le> (\<approx>\<^sub>\<flat>)"
  sorry

lemma basic_weak_receive_preservation: "(\<And>x. P x \<approx>\<^sub>\<flat> Q x) \<Longrightarrow> a \<triangleright> x. P x \<approx>\<^sub>\<flat> a \<triangleright> x. Q x"
  sorry

lemma basic_weak_parallel_preservation_left: "p\<^sub>1 \<approx>\<^sub>\<flat> p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<parallel> q \<approx>\<^sub>\<flat> p\<^sub>2 \<parallel> q"
  sorry

lemma basic_weak_parallel_preservation_right: "q\<^sub>1 \<approx>\<^sub>\<flat> q\<^sub>2 \<Longrightarrow> p \<parallel> q\<^sub>1 \<approx>\<^sub>\<flat> p \<parallel> q\<^sub>2"
  sorry

lemma basic_weak_parallel_preservation: "\<lbrakk>p\<^sub>1 \<approx>\<^sub>\<flat> p\<^sub>2; q\<^sub>1 \<approx>\<^sub>\<flat> q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<approx>\<^sub>\<flat> p\<^sub>2 \<parallel> q\<^sub>2"
  sorry

lemma basic_weak_new_channel_preservation: "(\<And>a. P a \<approx>\<^sub>\<flat> Q a) \<Longrightarrow> \<nu> a. P a \<approx>\<^sub>\<flat> \<nu> a. Q a"
  sorry

quotient_type basic_weak_behavior = process / "(\<approx>\<^sub>\<flat>)"
  using basic.weak.bisimilarity_is_equivalence .

declare basic_weak_behavior.abs_eq_iff [equivalence_transfer]

(* FIXME:
  Once #14 is resolved, the following should be done based on \<open>natural_transition_system\<close>, like in
  the strong case.
*)
context begin

private
  lift_definition stop' :: basic_weak_behavior
  is Stop .

private
  lift_definition send' :: "[chan, val] \<Rightarrow> basic_weak_behavior"
  is Send .

private
  lift_definition receive' :: "[chan, val \<Rightarrow> basic_weak_behavior] \<Rightarrow> basic_weak_behavior"
  is Receive
  using basic_weak_receive_preservation .

private
  lift_definition parallel' :: "[basic_weak_behavior, basic_weak_behavior] \<Rightarrow> basic_weak_behavior"
  is Parallel
  using basic_weak_parallel_preservation .

private
  lift_definition new_channel' :: "(chan \<Rightarrow> basic_weak_behavior) \<Rightarrow> basic_weak_behavior"
  is NewChannel
  using basic_weak_new_channel_preservation .

private
  lift_definition guard' :: "[bool, basic_weak_behavior] \<Rightarrow> basic_weak_behavior"
  is guard
  sorry

private
  lift_definition general_parallel' :: "['a \<Rightarrow> basic_weak_behavior, 'a list] \<Rightarrow> basic_weak_behavior"
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
