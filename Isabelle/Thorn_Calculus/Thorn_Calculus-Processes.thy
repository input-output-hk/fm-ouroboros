section \<open>Processes\<close>

theory "Thorn_Calculus-Processes"
imports
  "Relation_Methods.Equivalence"
  "Transition_Systems-New.Transition_Systems-Foundations" \<comment> \<open>for the \<^const>\<open>compower\<close> notation\<close>
  "Thorn_Calculus-Foundations"
  "HOL-Library.BNF_Corec"
begin

ML_file \<open>binder_preservation.ML\<close>

codatatype process =
  Stop |
  Send \<open>chan\<close> \<open>val\<close> |
  Receive \<open>chan\<close> \<open>val \<Rightarrow> process\<close> |
  Parallel \<open>process\<close> \<open>process\<close> |
  NewChannel \<open>chan \<Rightarrow> process\<close>

definition
  stop :: "process family" (\<open>\<zero>\<close>)
where
  [simp]: "stop = (\<lambda>_. Stop)"
definition
  send :: "chan family \<Rightarrow> val family \<Rightarrow> process family" (infix \<open>\<triangleleft>\<close> 52)
where
  [simp]: "send A X = (\<lambda>e. Send (A e) (X e))"
definition
  receive :: "chan family \<Rightarrow> (val \<Rightarrow> process family) \<Rightarrow> process family"
where
  [simp]: "receive A \<P> = (\<lambda>e. Receive (A e) (\<lambda>x. \<P> x e))"
definition
  parallel :: "process family \<Rightarrow> process family \<Rightarrow> process family" (infixr \<open>\<parallel>\<close> 51)
where
  [simp]: "parallel P Q = (\<lambda>e. Parallel (P e) (Q e))"
definition
  new_channel :: "(chan \<Rightarrow> process family) \<Rightarrow> process family" (binder \<open>\<nu> \<close> 52)
where
  [simp]: "new_channel \<P> = (\<lambda>e. NewChannel (\<lambda>a. \<P> a e))"

text \<open>
  The notation for \<^const>\<open>receive\<close> cannot be declared with @{theory_text \<open>binder\<close>}, for the
  following reasons:

    \<^item> It does not allow binding multiple variables in one go (like in \<open>\<forall>x\<^sub>1 \<dots> x\<^sub>n. _\<close>).

    \<^item> It has an extra parameter (for the channel family) before the binder.

  Therefore we introduce this notation using the low-level @{theory_text \<open>syntax\<close>},
  @{theory_text \<open>translations\<close>}, and @{theory_text \<open>print_translation\<close>} constructs.
\<close>

syntax
  "_receive" :: "chan family \<Rightarrow> pttrn \<Rightarrow> process family \<Rightarrow> process family"
  (\<open>(3_ \<triangleright> _./ _)\<close> [53, 0, 52] 52)
translations
  "A \<triangleright> x. P" \<rightleftharpoons> "CONST receive A (\<lambda>x. P)"
print_translation \<open>
  [preserve_binder_abs_receive_tr' @{const_syntax receive} @{syntax_const "_receive"}]
\<close>

friend_of_corec receive :: "chan family \<Rightarrow> (val \<Rightarrow> process family) \<Rightarrow> process family" where
  "receive A \<P> e = Receive (A e) (\<lambda>x. \<P> x e)"
  by (simp only: receive_def, transfer_prover)

friend_of_corec parallel :: "process family \<Rightarrow> process family \<Rightarrow> process family" where
  "parallel P Q e = Parallel (P e) (Q e)"
  by (simp only: parallel_def, transfer_prover)

friend_of_corec new_channel :: "(chan \<Rightarrow> process family) \<Rightarrow> process family" where
  "new_channel \<P> e = NewChannel (\<lambda>a. \<P> a e)"
  by (simp only: new_channel_def, transfer_prover)

(* FIXME: Mention that \<open>\<circ>\<close> binds stronger than all the above operators and binders. *)

lemma process_family_distinctnesses [induct_simp]:
  shows
    "\<zero> \<noteq> A \<triangleleft> X"
  and
    "A \<triangleleft> X \<noteq> \<zero>"
  and
    "\<zero> \<noteq> A \<triangleright> x. \<P> x"
  and
    "A \<triangleright> x. \<P> x \<noteq> \<zero>"
  and
    "\<zero> \<noteq> P \<parallel> Q"
  and
    "P \<parallel> Q \<noteq> \<zero>"
  and
    "\<zero> \<noteq> \<nu> a. \<Q> a"
  and
    "\<nu> a. \<Q> a \<noteq> \<zero>"
  and
    "A \<triangleleft> X \<noteq> B \<triangleright> x. \<P> x"
  and
    "A \<triangleright> x. \<P> x \<noteq> B \<triangleleft> X"
  and
    "A \<triangleleft> X \<noteq> P \<parallel> Q"
  and
    "P \<parallel> Q \<noteq> A \<triangleleft> X"
  and
    "A \<triangleleft> X \<noteq> \<nu> a. \<Q> a"
  and
    "\<nu> a. \<Q> a \<noteq> A \<triangleleft> X"
  and
    "A \<triangleright> x. \<P> x \<noteq> P \<parallel> Q"
  and
    "P \<parallel> Q \<noteq> A \<triangleright> x. \<P> x"
  and
    "A \<triangleright> x. \<P> x \<noteq> \<nu> a. \<Q> a"
  and
    "\<nu> a. \<Q> a \<noteq> A \<triangleright> x. \<P> x"
  and
    "P \<parallel> Q \<noteq> \<nu> a. \<Q> a"
  and
    "\<nu> a. \<Q> a \<noteq> P \<parallel> Q"
  by (auto dest: fun_cong)

text \<open>
  Note that the above injectivity statements are not exhaustive, as they do not cover process
  families that are exotic at the top level. Therefore, if such process families occur, these
  injectivity statements are of no help.
\<close>

lemma process_family_injectivities [induct_simp]:
  shows
    "A\<^sub>1 \<triangleleft> X\<^sub>1 = A\<^sub>2 \<triangleleft> X\<^sub>2 \<longleftrightarrow> A\<^sub>1 = A\<^sub>2 \<and> X\<^sub>1 = X\<^sub>2"
  and
    "A\<^sub>1 \<triangleright> x. \<P>\<^sub>1 x = A\<^sub>2 \<triangleright> x. \<P>\<^sub>2 x \<longleftrightarrow> A\<^sub>1 = A\<^sub>2 \<and> \<P>\<^sub>1 = \<P>\<^sub>2"
  and
    "P\<^sub>1 \<parallel> Q\<^sub>1 = P\<^sub>2 \<parallel> Q\<^sub>2 \<longleftrightarrow> P\<^sub>1 = P\<^sub>2 \<and> Q\<^sub>1 = Q\<^sub>2"
  and
    "\<nu> a. \<Q>\<^sub>1 a = \<nu> a. \<Q>\<^sub>2 a \<longleftrightarrow> \<Q>\<^sub>1 = \<Q>\<^sub>2"
  by (auto dest: fun_cong)

definition create_channel :: "process family \<Rightarrow> process family" (\<open>\<star>\<close>) where
  [simp]: "\<star> = new_channel \<circ> \<Delta>"

lemma new_channel_as_create_channel:
  "new_channel = \<star> \<circ> \<nabla>"
  by auto

text \<open>
  The following trivially provable lemmas are stated, because they are later used as
  pre-simplification rules.
\<close>

lemma family_uncurry_after_stop:
  shows "\<nabla> (\<lambda>_. \<zero>) = \<zero>"
  by simp

lemma family_uncurry_after_send:
  shows "\<nabla> (\<lambda>b. \<A> b \<triangleleft> X b) = \<nabla> \<A> \<triangleleft> \<nabla> X"
  by simp

lemma family_uncurry_after_receive:
  shows "\<nabla> (\<lambda>b. \<A> b \<triangleright> x. \<P> x b) = \<nabla> \<A> \<triangleright> x. \<nabla> (\<P> x)"
  by simp

lemma family_uncurry_after_parallel:
  shows "\<nabla> (\<lambda>a. \<P> a \<parallel> \<Q> a) = \<nabla> \<P> \<parallel> \<nabla> \<Q>"
  by simp

lemma family_uncurry_after_new_channel:
  shows "\<nabla> (\<lambda>a. \<nu> b. \<P> a b) = \<nu> b. \<nabla> (\<lambda>a. \<P> a b)"
  by simp

text \<open>
  The following trivially provable lemmas are stated, because two of them are used by the
  \<^theory_text>\<open>de_bruijn\<close> method and one of them is used in \<^theory_text>\<open>Thorn_Calculus-Core_Bisimilarities\<close>.
\<close>

lemma deep_uncurry_after_parallel:
  shows "\<nabla>\<^bsub>i\<^esub> (\<lambda>a. \<P> a \<parallel> \<Q> a) = \<nabla>\<^bsub>i\<^esub> \<P> \<parallel> \<nabla>\<^bsub>i\<^esub> \<Q>"
  by simp

lemma deep_uncurry_after_new_channel:
  shows "\<nabla>\<^bsub>i\<^esub> (\<lambda>a. \<nu> b. \<P> a b) = \<nu> b. \<nabla>\<^bsub>i\<^esub> (\<lambda>a. \<P> a b)"
  by simp

lemma deep_uncurry_after_create_channel:
  shows "\<nabla>\<^bsub>i\<^esub> (\<lambda>a. \<star> (\<P> a)) = \<star> (\<nabla>\<^bsub>Suc i\<^esub> \<P>)"
  by simp

lemma adapted_after_stop:
  shows "\<zero> \<guillemotleft> \<E> = \<zero>"
  by transfer (simp add: comp_def)

lemma adapted_after_send:
  shows "(A \<triangleleft> X) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<triangleleft> X \<guillemotleft> \<E>"
  by transfer (simp add: comp_def)

lemma adapted_after_receive:
  shows "(A \<triangleright> x. \<P> x) \<guillemotleft> \<E> = A \<guillemotleft> \<E> \<triangleright> x. \<P> x \<guillemotleft> \<E>"
  by transfer (simp add: comp_def)

lemma adapted_after_parallel:
  shows "(P \<parallel> Q) \<guillemotleft> \<E> = P \<guillemotleft> \<E> \<parallel> Q \<guillemotleft> \<E>"
  by transfer (simp add: comp_def)

lemma adapted_after_new_channel:
  shows "(\<nu> a. \<Q> a) \<guillemotleft> \<E> = \<nu> a. \<Q> a \<guillemotleft> \<E>"
  by transfer (simp add: comp_def)

lemma adapted_after_create_channel:
  shows "\<star> P \<guillemotleft> \<E> = \<star> (P \<guillemotleft> on_tail \<E>)"
  unfolding on_tail_def
  by transfer (simp add: comp_def)

lemma adapted_after_create_channel_power:
  shows "\<star>\<^bsup>n\<^esup> P \<guillemotleft> \<E> = \<star>\<^bsup>n\<^esup> (P \<guillemotleft> on_suffix n \<E>)"
proof (induction n arbitrary: \<E>)
  case 0
  then show ?case
    by (simp add: identity_as_partial_on_suffix [symmetric])
next
  case (Suc n \<E>)
  show ?case
  proof -
    have "\<star>\<^bsup>Suc n\<^esup> P \<guillemotleft> \<E> = \<star> (\<star>\<^bsup>n\<^esup> P) \<guillemotleft> \<E>"
      by simp
    also have "\<dots> = \<star> (\<star>\<^bsup>n\<^esup> P \<guillemotleft> on_tail \<E>)"
      by (simp only: adapted_after_create_channel)
    also have "\<dots> = \<star> (\<star>\<^bsup>n\<^esup> (P \<guillemotleft> on_suffix n (on_tail \<E>)))"
      by (simp only: Suc.IH)
    also have "\<dots> = \<star> (\<star>\<^bsup>n\<^esup> (P \<guillemotleft> on_suffix (Suc n) \<E>))"
      unfolding on_tail_def
      using composition_as_partial_on_suffix [THEN fun_cong]
      by simp
    also have "\<dots> = \<star>\<^bsup>Suc n\<^esup> (P \<guillemotleft> on_suffix (Suc n) \<E>)"
      by simp
    finally show ?thesis .
  qed
qed

text \<open>
  The next set of lemmas states that a process that can be constructed both via a lifted data
  constructor and via adaptation can be constructed by applying the lifted data constructor to
  adaptations and also by adapting an application of the lifted data constructor.
\<close>
(* FIXME:
  \<^item> Check whether ``lifted data constructor'' is the right term (it sounds bulky).

  \<^item> Phrase this whole text in a more crisp way.

  \<^item> Rename the lemmas below to reflect the pattern described above.
*)

lemma stop_and_adapted:
  assumes "\<zero> = S \<guillemotleft> \<E>"
  shows "S = \<zero>"
  using adapted_undo and assms
  unfolding stop_def
  by (metis comp_def)

lemma send_and_adapted:
  assumes "A' \<triangleleft> X' = S \<guillemotleft> \<E>"
  obtains A and X where "A' = A \<guillemotleft> \<E>" and "X' = X \<guillemotleft> \<E>" and "S = A \<triangleleft> X"
proof -
  from assms have S_definition: "S = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<triangleleft> X' \<circ> inv \<lfloor>\<E>\<rfloor>"
    using adapted_undo
    unfolding send_def
    by (metis comp_def)
  moreover
  from assms [symmetric] and S_definition have "A' = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>" and "X' = X' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>"
    by (simp_all only: adapted_after_send process_family_injectivities)
  ultimately show ?thesis
    using that
    by simp
qed

lemma receive_and_adapted:
  assumes "A' \<triangleright> x. \<P>' x = S \<guillemotleft> \<E>"
  obtains A and \<P> where "A' = A \<guillemotleft> \<E>" and "\<P>' = (\<lambda>x. \<P> x \<guillemotleft> \<E>)" and "S = A \<triangleright> x. \<P> x"
proof -
  have "S = S \<guillemotleft> \<E> \<circ> inv \<lfloor>\<E>\<rfloor>"
    by (simp only: adapted_undo)
  also have "\<dots> = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<triangleright> x. \<P>' x \<circ> inv \<lfloor>\<E>\<rfloor>"
    by (simp only: assms [symmetric] receive_def comp_def)
  finally have S_definition: "S = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<triangleright> x. \<P>' x \<circ> inv \<lfloor>\<E>\<rfloor>" .
  moreover
  from assms [symmetric] and S_definition
  have "A' = A' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>" and "\<P>' = (\<lambda>x. \<P>' x \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>)"
    by (simp_all only: adapted_after_receive process_family_injectivities)
  ultimately show ?thesis
    using that [where \<P> = "\<lambda>x. \<P>' x \<circ> inv \<lfloor>\<E>\<rfloor>"]
    by blast
qed

lemma parallel_and_adapted:
  assumes "P' \<parallel> Q' = S \<guillemotleft> \<E>"
  obtains P and Q where "P' = P \<guillemotleft> \<E>" and "Q' = Q \<guillemotleft> \<E>" and "S = P \<parallel> Q"
proof -
  from assms have S_definition: "S = P' \<circ> inv \<lfloor>\<E>\<rfloor> \<parallel> Q' \<circ> inv \<lfloor>\<E>\<rfloor>"
    using adapted_undo
    unfolding parallel_def
    by (metis comp_def)
  moreover
  from assms [symmetric] and S_definition have "P' = P' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>" and "Q' = Q' \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>"
    by (simp_all only: adapted_after_parallel process_family_injectivities)
  ultimately show ?thesis
    using that
    by simp
qed

lemma new_channel_and_adapted:
  assumes "\<nu> a. \<P>' a = S \<guillemotleft> \<E>"
  obtains \<P> where "\<P>' = (\<lambda>a. \<P> a \<guillemotleft> \<E>)" and "S = \<nu> a. \<P> a"
proof -
  have "S = S \<guillemotleft> \<E> \<circ> inv \<lfloor>\<E>\<rfloor>"
    by (simp only: adapted_undo)
  also have "\<dots> = \<nu> a. \<P>' a \<circ> inv \<lfloor>\<E>\<rfloor>"
    by (simp only: assms [symmetric] new_channel_def comp_def)
  finally have S_definition: "S = \<nu> a. \<P>' a \<circ> inv \<lfloor>\<E>\<rfloor>" .
  moreover
  from assms [symmetric] and S_definition have "\<P>' = (\<lambda>a. \<P>' a \<circ> inv \<lfloor>\<E>\<rfloor> \<guillemotleft> \<E>)"
    by (simp_all only: adapted_after_new_channel process_family_injectivities)
  ultimately show ?thesis
    using that [where \<P> = "\<lambda>a. \<P>' a \<circ> inv \<lfloor>\<E>\<rfloor>"]
    by simp
qed

(*FIXME:
  The following lemmas and all the other \<^theory_text>\<open>environment_dependent\<close> lemmas seem to be used only in the
  manual rewriting under \<open>\<triangleright>\<^sup>\<infinity>\<close> and thus should be removed once the new implementation of
  \<^theory_text>\<open>equivalence\<close> is in place.
*)

(*FIXME:
  If we ever add some sort of wrapping to the statements of the following lemmas in order to make
  tools that try to rewrite repeatedly not hang, we should probably also add
  \<^theory_text>\<open>environment_dependent_stop\<close>.
*)

lemma environment_dependent_send:
  shows "(\<lambda>e. (\<A> e \<triangleleft> \<X> e) e) = (\<lambda>e. \<A> e e) \<triangleleft> (\<lambda>e. \<X> e e)"
  by (simp only: send_def)

lemma environment_dependent_receive:
  shows "(\<lambda>e. (\<A> e \<triangleright> x. \<P> x e) e) = (\<lambda>e. \<A> e e) \<triangleright> x. (\<lambda>e. \<P> x e e)"
  by (simp only: receive_def)

lemma environment_dependent_parallel:
  shows "(\<lambda>e. (\<P> e \<parallel> \<Q> e) e) = (\<lambda>e. \<P> e e) \<parallel> (\<lambda>e. \<Q> e e)"
  by (simp only: parallel_def)

(*FIXME:
  Perhaps we should add \<^theory_text>\<open>environment_dependent_new_channel\<close>, if only for completeness.
*)

(*FIXME:
  Perhaps add \<^theory_text>\<open>environment_dependent\<close> lemmas also for higher-level constructs like the ones from
  \<^theory_text>\<open>Thorn_Calculus-Communication\<close>.
*)

text \<open>
  We define guarding of processes at the host-language level.
\<close>

definition guard :: "bool \<Rightarrow> process family \<Rightarrow> process family" (infixr \<open>?\<close> 52) where
  [simp]: "v ? P = (if v then P else \<zero>)"

(*FIXME: Add \<^theory_text>\<open>friend_of_corec\<close> declaration for \<open>guard\<close>. *)

(*FIXME: Perhaps add \<^theory_text>\<open>environment_dependent_guard\<close>.*)

lemma adapted_after_guard:
  shows "(v ? P) \<guillemotleft> \<E> = v ? P \<guillemotleft> \<E>"
  by transfer (simp add: comp_def)

text \<open>
  We define parallel composition over a list of processes families.
\<close>

primrec general_parallel :: "('a \<Rightarrow> process family) \<Rightarrow> 'a list \<Rightarrow> process family" where
  "general_parallel _ [] = \<zero>" |
  "general_parallel \<P> (v # vs) = \<P> v \<parallel> general_parallel \<P> vs"

text \<open>
  We define a notation for repeated parallel composition combined with mapping. Since this notation
  clashes with \<open>HOL.Groups_List._prod_list\<close>, we have to remove the latter.
\<close>

no_syntax
  "_prod_list" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" (\<open>(3\<Prod>_\<leftarrow>_. _)\<close> [0, 51, 10] 10)
syntax
  "_general_parallel" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> process \<Rightarrow> process" (\<open>(3\<Prod>_\<leftarrow>_. _)\<close> [0, 0, 52] 52)
translations
  "\<Prod>v\<leftarrow>vs. P" \<rightleftharpoons> "CONST general_parallel (\<lambda>v. P) vs"
print_translation \<open>
  [
    preserve_binder_abs_general_parallel_tr'
      @{const_syntax general_parallel}
      @{syntax_const "_general_parallel"}
  ]
\<close>

(*FIXME: Add \<^theory_text>\<open>friend_of_corec\<close> declaration for \<open>general_parallel\<close>. *)

lemma adapted_after_general_parallel:
  shows "(\<Prod>v \<leftarrow> vs. \<P> v) \<guillemotleft> \<E> = \<Prod>v \<leftarrow> vs. \<P> v \<guillemotleft> \<E>"
  by
    (induction vs)
    (simp_all only: general_parallel.simps adapted_after_stop adapted_after_parallel)

lemma environment_dependent_general_parallel:
  shows "(\<lambda>e. (\<Prod>v \<leftarrow> vs. \<P> v e) e) = \<Prod>v \<leftarrow> vs. (\<lambda>e. \<P> v e e)"
proof (induction vs)
  case Nil
  show ?case
    by (simp only: general_parallel.simps(1))
next
  case Cons
  then show ?case
    unfolding general_parallel.simps(2)
    by (subst environment_dependent_parallel, simp only:)
qed

lemma general_parallel_conversion_deferral:
  shows "\<Prod>w \<leftarrow> map f vs. \<P> w = \<Prod>v \<leftarrow> vs. \<P> (f v)"
  by (induction vs) simp_all

(*FIXME: Consider permitting tags of arbitrary types that have a total order. *)

definition tagged_new_channel :: "nat \<Rightarrow> (chan \<Rightarrow> process family) \<Rightarrow> process family" where
  [simp]: "tagged_new_channel _ \<P> = \<nu> a. \<P> a"

syntax
  "_tagged_new_channel" :: "[nat, pttrn, process family] \<Rightarrow> process family"
  (\<open>(3\<langle>_\<rangle> \<nu> _./ _)\<close> [0, 0, 52] 52)
translations
  "\<langle>t\<rangle> \<nu> a. P" \<rightleftharpoons> "CONST tagged_new_channel t (\<lambda>a. P)"
print_translation \<open>
  [
    preserve_binder_abs_receive_tr'
      @{const_syntax tagged_new_channel}
      @{syntax_const "_tagged_new_channel"}
  ]
\<close>

definition tagged_create_channel :: "nat \<Rightarrow> process family \<Rightarrow> process family" (\<open>\<langle>_\<rangle> \<star>\<close>) where
  [simp]: "\<langle>_\<rangle> \<star> = \<star>"

text \<open>
  \<^theory_text>\<open>de_bruijn\<close> expects there to be no chained facts. With chained facts present, there would be two
  issues:

    \<^item> The @{method simp} invocation would insert the chained facts as premises, which would be good.
      However, @{method simp} would not finish successfully when no simplification is possible, and
      thus the insertion of the chained fact would not happen in this case.

    \<^item> The @{method unfold} invocation, when successful, would insert the chained facts a second
      time (which could be prevented with \<^theory_text>\<open>use in\<close>, of course).
\<close>

(*FIXME:
  The implementation of \<^theory_text>\<open>de_bruijn\<close>, in particular the use and handling of \<open>remove\<close> adaptations, is
  very ad-hoc and brittle and thus should be reworked.
*)

method de_bruijn = (
  (
    simp only:
      new_channel_as_create_channel [unfolded comp_def]
      family_uncurry_as_deep_uncurry [where 'a = process]
      deep_uncurry_after_parallel
      deep_uncurry_after_create_channel
      deep_uncurry_reordering [where 'a = process]
  )?,
  (
    unfold
      family_uncurry_as_deep_uncurry [where 'a = process, symmetric]
      constant_function_family_uncurry_as_remove_adapted [where 'a = process]
      remove_adapted_after_family_uncurry [where 'a = process, symmetric]
      adapted_after_stop [where \<E> = "remove _"]
  )?
)

(*FIXME: Come up with an appropriate handling of \<open>\<triangleleft>\<close> and custom processes like bridges. *)

text \<open>
  The @{method de_bruijn} method can solve trivial goals, because it uses @{method simp}. However,
  this should not happen when the goal contains bisimilarities, as no rules for solving these are
  given above.

  Also note that it copies the chained fact into the goal as premises, like @{method simp} does
  (which it internally uses).
\<close>

definition
  process_family_uncurry_relation :: "(chan \<Rightarrow> process family) \<Rightarrow> process family \<Rightarrow> bool"
where
  [simp]: "process_family_uncurry_relation \<P> P = (P = \<nabla> \<P>)"

lemma process_family_uncurry_relation_bi_uniqueness [transfer_rule]:
  shows "bi_unique process_family_uncurry_relation"
  using family_uncurry_is_bijective
  by (auto simp only: bij_def inj_def bi_unique_def process_family_uncurry_relation_def)

lemma process_family_uncurry_relation_bi_totality [transfer_rule]:
  shows "bi_total process_family_uncurry_relation"
  using family_uncurry_is_bijective
  by (auto simp only: bij_def surj_def bi_total_def process_family_uncurry_relation_def)

lemma process_family_uncurry_relation_right_uniqueness [transfer_rule]:
  shows "right_unique process_family_uncurry_relation"
  using process_family_uncurry_relation_bi_uniqueness
  by (simp add: bi_unique_def right_unique_def)

lemma process_family_uncurry_relation_right_totality [transfer_rule]:
  shows "right_total process_family_uncurry_relation"
  using process_family_uncurry_relation_bi_totality
  by (simp add: bi_total_def right_total_def)

lemma process_family_uncurry_transfer [transfer_rule]:
  shows "rel_fun process_family_uncurry_relation (=) \<nabla> (\<lambda>P. P)"
  by (simp add: rel_fun_def)

text \<open>
  \<^theory_text>\<open>process_family_uncurry_elimination\<close> expects there to be no chained facts.
\<close>

method process_family_uncurry_elimination uses in_process_prem processed_prems = (
  match in_process_prem in "V (\<nabla> :: (chan \<Rightarrow> process family) \<Rightarrow> process family)" (cut) for V \<Rightarrow> \<open>
    match (V) in
      "\<lambda>_. ?v" (cut) \<Rightarrow> \<open>
        process_family_uncurry_elimination
          processed_prems: processed_prems in_process_prem
      \<close> \<bar>
      _ (cut) \<Rightarrow> \<open>
        process_family_uncurry_elimination
          in_process_prem: in_process_prem [transferred]
          processed_prems: processed_prems
      \<close>
      \<comment> \<open>
        This technique involving \<^theory_text>\<open>cut\<close> relies on higher-order unification to yield a non-constant
        matching function first if such a function exists.
      \<close>
  \<close> |
  match premises in prem [thin]: _ (cut) \<Rightarrow> \<open>
    (match premises in others [thin]: _ (cut, multi) \<Rightarrow> \<open>insert others\<close>)?,
      \<comment> \<open>
        This is done, because apparently thinning does not work across recursive method calls.
      \<close>
    process_family_uncurry_elimination in_process_prem: prem processed_prems: processed_prems
  \<close> |
  insert processed_prems
)

definition wrapped_remove_adapted :: "process family \<Rightarrow> nat \<Rightarrow> process family" where
  [simp]: "wrapped_remove_adapted P i = P \<guillemotleft> remove i"

text \<open>
  We do not perform rewriting of the facts in @{attribute equivalence}. This is not necessary for
  the approach we are following here, where the only facts in @{attribute equivalence} are
  equivalence inclusions.
\<close>

method process_family_equivalence = (
  -,
  use in \<open>
    de_bruijn;
    process_family_uncurry_elimination,
    (fold wrapped_remove_adapted_def)?,
    equivalence
  \<close>
)

(*FIXME: Currently, \<^theory_text>\<open>process_family_equivalence\<close> does not work with tags. *)

end
