section \<open>Proper Transition System\<close>

theory Proper_Transition_System
  imports Basic_Transition_System
begin

subsection \<open>Actions\<close>

text \<open>
  Actions include input actions and the internal action.
\<close>

datatype proper_action =
  ProperIn \<open>chan\<close> \<open>val\<close> (infix "\<triangleright>" 100) |
  ProperInternal ("\<tau>")

text \<open>
  Each action in the proper transition system corresponds to an action in the basic transition
  system.
\<close>

primrec basic_action_of :: "proper_action \<Rightarrow> basic_action" where
  "basic_action_of (a \<triangleright> x) = a \<triangleright> x" |
  "basic_action_of \<tau> = \<tau>"

subsection \<open>Output Rests\<close>

text \<open>
  An output rest bundles the scope openings, the output value, and the target process of an output
  transition. Its syntax is part of the syntax of output transitions.
\<close>

datatype 'p output_rest =
  WithoutOpening \<open>val\<close> \<open>'p\<close> ("_\<rparr> _" [52, 51] 51) |
  WithOpening \<open>chan \<Rightarrow> 'p output_rest\<close> (binder "\<nu> " 51)

text \<open>
  Note that the definition of \<open>output_rest\<close> is actually more permissive than the verbal definition
  of output rests above: the number of scope openings of a particular \<open>output_rest\<close> value is not
  necessarily fixed, since the structure of a follow-up output rest in a \<open>WithOpening\<close> value can
  depend on the given channel. This is just to keep the definition simple. It does not cause any
  problems in our later proofs.
\<close>

text \<open>
  We introduce the alias \<open>output_rest_lift\<close> for the automatically generated relator
  \<^const>\<open>rel_output_rest\<close>. Furthermore we provide alternative names for some facts related to
  \<open>output_rest_lift\<close>, which resemble the names that would be used for these facts if
  \<open>output_rest_lift\<close> was defined by hand via @{theory_text inductive}.
\<close>

abbreviation
  output_rest_lift :: "(['p, 'q] \<Rightarrow> bool) \<Rightarrow> (['p output_rest, 'q output_rest] \<Rightarrow> bool)"
where
  "output_rest_lift \<equiv> rel_output_rest"

lemmas output_rest_lift_intros = output_rest.rel_intros
lemmas without_opening_lift = output_rest_lift_intros(1)
lemmas with_opening_lift = output_rest_lift_intros(2)
lemmas output_rest_lift_cases = output_rest.rel_cases

text \<open>
  Interestingly, equipping \<^type>\<open>output_rest\<close> with \<^const>\<open>output_rest_lift\<close> leads to a residual
  structure, despite the fact that output rests are not intended to serve as residuals but only as
  components of residuals.
\<close>

interpretation output_rest: residual output_rest_lift
  by
    unfold_locales
    (
      fact output_rest.rel_mono,
      fact output_rest.rel_eq,
      fact output_rest.rel_compp,
      fact output_rest.rel_conversep
    )

subsection \<open>Residuals\<close>

text \<open>
  There are two kinds of residuals in the proper transition system: simple residuals, written
  \<open>\<lparr>\<delta>\<rparr> q\<close> where \<open>\<delta>\<close> is an action, and output residuals, written
  \<open>\<lparr>a \<triangleleft> \<nu> b\<^sub>1 \<dots> b\<^sub>n. X b\<^sub>1 \<dots> b\<^sub>n\<rparr> Q b\<^sub>1 \<dots> b\<^sub>n\<close> where \<open>a\<close> is a channel and the \<open>b\<^sub>i\<close> are channel variables.
\<close>

datatype 'p proper_residual =
  Simple \<open>proper_action\<close> \<open>'p\<close> ("\<lparr>_\<rparr> _" [0, 51] 51) |
  Output \<open>chan\<close> \<open>'p output_rest\<close> ("\<lparr>_ \<triangleleft> _" [0, 51] 51)

text \<open>
  We introduce the alias \<open>proper_lift\<close> for the automatically generated relator
  \<^const>\<open>rel_proper_residual\<close>. Furthermore we provide alternative names for some facts related to
  \<open>proper_lift\<close>, which resemble the names that would be used for these facts if \<open>proper_lift\<close> was
  defined by hand via @{theory_text inductive}.
\<close>

abbreviation
  proper_lift :: "(['p, 'q] \<Rightarrow> bool) \<Rightarrow> (['p proper_residual, 'q proper_residual] \<Rightarrow> bool)"
where
  "proper_lift \<equiv> rel_proper_residual"

lemmas proper_lift_intros = proper_residual.rel_intros
lemmas simple_lift = proper_lift_intros(1)
lemmas output_lift = proper_lift_intros(2)
lemmas proper_lift_cases = proper_residual.rel_cases

text \<open>
  Equipping \<^type>\<open>proper_residual\<close> with \<^const>\<open>proper_lift\<close> leads to a residual structure.
\<close>

interpretation proper: residual proper_lift
  by
    unfold_locales
    (
      fact proper_residual.rel_mono,
      fact proper_residual.rel_eq,
      fact proper_residual.rel_compp,
      fact proper_residual.rel_conversep
    )

subsection \<open>Transition System\<close>

text \<open>
  The following definition of the transition relation captures the set of rules that define the
  transition system.
\<close>

inductive
  proper_transition :: "process \<Rightarrow> process proper_residual \<Rightarrow> bool"
  (infix "\<rightarrow>\<^sub>\<sharp>" 50)
where
  simple:
    "p \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> q" |
  output_without_opening:
    "p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> x\<rparr> q" |
  output_with_opening:
    "\<lbrakk> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b; \<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> K b \<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. K b"

text \<open>
  The residual structure and \<^const>\<open>proper_transition\<close> together form a transition system.
\<close>

interpretation proper: transition_system proper_lift proper_transition
  by intro_locales

text \<open>
  We introduce concise notation for some of the derived predicates of the transition system.
\<close>

notation proper.pre_bisimilarity (infix "\<lesssim>\<^sub>\<sharp>" 50)
notation proper.bisimilarity (infix "\<sim>\<^sub>\<sharp>" 50)

subsection \<open>Fundamental Properties of the Transition System\<close>

lemma no_proper_transitions_from_stop: "\<not> \<zero> \<rightarrow>\<^sub>\<sharp>c"
proof
  fix c
  assume "\<zero> \<rightarrow>\<^sub>\<sharp>c"
  then show False
    by cases (simp_all add: no_basic_transitions_from_stop)
qed

subsection \<open>Relationships between Basic and Proper Bisimilarity\<close>

lemma basic_bisimilarity_is_proper_simulation: "proper.sim (\<sim>\<^sub>\<flat>)"
proof proper.is_simulation_standard
  case (sim p q c)
  then show ?case
  proof (induction arbitrary: q)
    case (simple p \<delta> p' q)
    from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> p'\<close>
    obtain q' where "q \<rightarrow>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
      using
        basic.bisimilarity_is_simulation and
        predicate2D and
        basic_lift_cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then show ?case
      by (blast intro: proper_transition.simple simple_lift)
  next
    case (output_without_opening p a x p' q)
    from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> p'\<close>
    obtain q' where "q \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
      using
        basic.bisimilarity_is_simulation and
        predicate2D and
        basic_lift_cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then show ?case
      by (blast intro: proper_transition.output_without_opening without_opening_lift output_lift)
  next
    case (output_with_opening p P a K q)
    obtain Q where "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<And>a. P a \<sim>\<^sub>\<flat> Q a"
    proof -
      from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close>
      obtain d where "q \<rightarrow>\<^sub>\<flat>d" and "basic_lift (\<sim>\<^sub>\<flat>) (\<lbrace>\<nu> a\<rbrace> P a) d"
        using basic.bisimilarity_is_simulation
        by blast
      from \<open>basic_lift (\<sim>\<^sub>\<flat>) (\<lbrace>\<nu> a\<rbrace> P a) d\<close> and \<open>q \<rightarrow>\<^sub>\<flat>d\<close> and that show ?thesis
        by cases (auto elim: rel_funE)
    qed
    (*
      In case we provide lemmas or proof methods for statements that we currently solve with smt,
      note that the above statement was formerly also proved using smt (after the dropping of
      contexts this surprisingly did not work anymore). Here is the old code:

          from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close>
          obtain Q where "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<And>a. P a \<sim>\<^sub>\<flat> Q a"
            using
              basic.bisimilarity_is_simulation and
              predicate2D and
              basic_lift.cases and
              basic_residual.distinct(1) and
              basic_residual.inject(2)
            by smt
    *)
    obtain L where "\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b" and "\<And>b. output_rest_lift (\<sim>\<^sub>\<flat>) (K b) (L b)"
    proof -
      from output_with_opening.IH and \<open>\<And>b. P b \<sim>\<^sub>\<flat> Q b\<close>
      have "\<forall>b. \<exists>l. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> l \<and> output_rest_lift (\<sim>\<^sub>\<flat>) (K b) l"
        using
          proper_lift_cases and
          proper_residual.distinct(1) and
          proper_residual.inject(2)
        by smt
      then have "\<exists>L. \<forall>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b \<and> output_rest_lift (\<sim>\<^sub>\<flat>) (K b) (L b)"
        by (fact choice)
      with that show ?thesis by blast
    qed
    from \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b\<close> and \<open>\<And>b. Q b \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> L b\<close> have "q \<rightarrow>\<^sub>\<sharp>\<lparr>a \<triangleleft> \<nu> b. L b"
      by (fact proper_transition.output_with_opening)
    with \<open>\<And>a. output_rest_lift (\<sim>\<^sub>\<flat>) (K a) (L a)\<close> show ?case
      using with_opening_lift and rel_funI and output_lift
      by smt
  qed
qed

lemma basic_bisimilarity_is_proper_bisimulation: "proper.bisim (\<sim>\<^sub>\<flat>)"
  using basic.bisimilarity_symmetry and basic_bisimilarity_is_proper_simulation
  by (fact proper.symmetric_simulation_is_bisimulation)

lemma basic_bisimilarity_in_proper_bisimilarity [equivalence]: "(\<sim>\<^sub>\<flat>) \<le> (\<sim>\<^sub>\<sharp>)"
  using basic_bisimilarity_is_proper_bisimulation
  by (fact proper.bisimulation_in_bisimilarity)

lemma basic_bisimilarity_in_proper_bisimilarity_rule: "p \<sim>\<^sub>\<flat> q \<Longrightarrow> p \<sim>\<^sub>\<sharp> q"
  using basic_bisimilarity_in_proper_bisimilarity ..

subsection \<open>The Basic Transition System as a Natural Transition System\<close>

lemma proper_receive_preservation: "(\<And>x. P x \<sim>\<^sub>\<sharp> Q x) \<Longrightarrow> a \<triangleright> x. P x \<sim>\<^sub>\<sharp> a \<triangleright> x. Q x"
  sorry

lemma proper_parallel_preservation_left: "p\<^sub>1 \<sim>\<^sub>\<sharp> p\<^sub>2 \<Longrightarrow> p\<^sub>1 \<parallel> q \<sim>\<^sub>\<sharp> p\<^sub>2 \<parallel> q"
  sorry

lemma proper_parallel_preservation_right: "q\<^sub>1 \<sim>\<^sub>\<sharp> q\<^sub>2 \<Longrightarrow> p \<parallel> q\<^sub>1 \<sim>\<^sub>\<sharp> p \<parallel> q\<^sub>2"
  sorry

lemma proper_parallel_preservation: "\<lbrakk>p\<^sub>1 \<sim>\<^sub>\<sharp> p\<^sub>2; q\<^sub>1 \<sim>\<^sub>\<sharp> q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<sim>\<^sub>\<sharp> p\<^sub>2 \<parallel> q\<^sub>2"
  sorry

lemma proper_new_channel_preservation: "(\<And>a. P a \<sim>\<^sub>\<sharp> Q a) \<Longrightarrow> \<nu> a. P a \<sim>\<^sub>\<sharp> \<nu> a. Q a"
  sorry

interpretation proper: natural_transition_system proper_lift proper_transition
  by
    unfold_locales
    (
      fact proper_receive_preservation,
      fact proper_parallel_preservation,
      fact proper_new_channel_preservation
    )

subsection \<open>Setup of the \<^theory_text>\<open>equivalence_simp\<close> Proof Method\<close>

quotient_type proper_behavior = process / "(\<sim>\<^sub>\<sharp>)"
  using proper.bisimilarity_is_equivalence .

declare proper_behavior.abs_eq_iff [equivalence_transfer]

context begin

private lift_definition stop' :: proper_behavior
  is Stop .

private lift_definition send' :: "[chan, val] \<Rightarrow> proper_behavior"
  is Send .

private lift_definition receive' :: "[chan, val \<Rightarrow> proper_behavior] \<Rightarrow> proper_behavior"
  is Receive
  using proper_receive_preservation .

private lift_definition parallel' :: "[proper_behavior, proper_behavior] \<Rightarrow> proper_behavior"
  is Parallel
  using proper_parallel_preservation .

private lift_definition new_channel' :: "(chan \<Rightarrow> proper_behavior) \<Rightarrow> proper_behavior"
  is NewChannel
  using proper_new_channel_preservation .

private lift_definition guard' :: "[bool, proper_behavior] \<Rightarrow> proper_behavior"
  is guard
  using proper.guard_preservation .

private lift_definition general_parallel' :: "['a \<Rightarrow> proper_behavior, 'a list] \<Rightarrow> proper_behavior"
  is general_parallel
  using proper.general_parallel_preservation .

lemmas [equivalence_transfer] =
  stop'.abs_eq
  send'.abs_eq
  receive'.abs_eq
  parallel'.abs_eq
  new_channel'.abs_eq
  guard'.abs_eq
  general_parallel'.abs_eq

end

subsection \<open>Conclusion\<close>

text \<open>
  This is all for the proper transition system.
\<close>

end
