section \<open>Proper Weak Transition System\<close>

theory Proper_Weak_Transition_System
  imports Basic_Weak_Transition_System Proper_Transition_System
begin

inductive proper_silent :: "[process, process proper_residual] \<Rightarrow> bool" where
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

notation proper.weak.pre_bisimilarity (infix "\<lessapprox>\<^sub>\<sharp>" 50)
notation proper.weak.bisimilarity (infix "\<approx>\<^sub>\<sharp>" 50)

(* NOTE:
  This will become obsolete once there is only one locale interpretation for the strong transition
  system.
*)
lemma basic_strong_bisimilarity_in_weak_bisimilarity: "(\<sim>\<^sub>\<sharp>) \<le> (\<approx>\<^sub>\<sharp>)"
  sorry

lemma basic_weak_bisimilarity_in_proper_weak_bisimilarity: "(\<approx>\<^sub>\<flat>) \<le> (\<approx>\<^sub>\<sharp>)"
  sorry

(* NOTE:
  Lemmas like the following should go away once we have a solution for automatically appyling facts
  like \<open>basic_weak_bisimilarity_in_proper_weak_bisimilarity\<close>.
*)

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

lemma proper_weak_receive_scope_extension: "a \<triangleright> x. \<nu> b. P x b \<approx>\<^sub>\<sharp> \<nu> b. a \<triangleright> x. P x b"
  sorry

lemma proper_weak_parallel_scope_extension_left: "\<nu> a. P a \<parallel> q \<approx>\<^sub>\<sharp> \<nu> a. (P a \<parallel> q)"
  sorry

lemma proper_weak_parallel_scope_extension_right: "p \<parallel> \<nu> a. Q a \<approx>\<^sub>\<sharp> \<nu> a. (p \<parallel> Q a)"
  sorry

lemma proper_weak_new_channel_scope_extension: "\<nu> b. \<nu> a. P a b \<approx>\<^sub>\<sharp> \<nu> a. \<nu> b. P a b"
  sorry

lemma proper_weak_parallel_unit_left: "\<zero> \<parallel> p \<approx>\<^sub>\<sharp> p"
  sorry

lemma proper_weak_parallel_unit_right: "p \<parallel> \<zero> \<approx>\<^sub>\<sharp> p"
  sorry

lemma proper_weak_parallel_commutativity: "p \<parallel> q \<approx>\<^sub>\<sharp> q \<parallel> p"
  sorry

lemma proper_weak_parallel_associativity: "(p \<parallel> q) \<parallel> r \<approx>\<^sub>\<sharp> p \<parallel> (q \<parallel> r)"
  sorry

lemma proper_weak_parallel_nested_commutativity: "p \<parallel> (q \<parallel> r) \<approx>\<^sub>\<sharp> q \<parallel> (p \<parallel> r)"
  sorry

subsection \<open>Equivalence Simplifier Setup\<close>

quotient_type proper_weak_behavior = process / "(\<approx>\<^sub>\<sharp>)"
  using proper.weak.bisimilarity_is_equivalence .

declare proper_weak_behavior.abs_eq_iff [equivalence_simp_goal_preparation]

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
  lift_definition map' :: "['a \<Rightarrow> proper_weak_behavior, 'a list] \<Rightarrow> proper_weak_behavior list"
  is map
  sorry

private
  lift_definition parallel_list' :: "proper_weak_behavior list \<Rightarrow> proper_weak_behavior"
  is parallel_list
  sorry

lemmas [equivalence_simp_goal_preparation] =
  stop'.abs_eq
  send'.abs_eq
  receive'.abs_eq
  parallel'.abs_eq
  new_channel'.abs_eq
  map'.abs_eq
  parallel_list'.abs_eq

end

lemmas [equivalence_simp] =
  proper_weak_receive_scope_extension
  proper_weak_parallel_scope_extension_left
  proper_weak_parallel_scope_extension_right
  proper_weak_new_channel_scope_extension
  proper_weak_parallel_unit_left
  proper_weak_parallel_unit_right
  proper_weak_parallel_associativity
  proper_weak_parallel_commutativity
  proper_weak_parallel_nested_commutativity

end
