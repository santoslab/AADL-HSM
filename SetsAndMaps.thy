theory SetsAndMaps
  imports Main
begin

definition opt_get :: "'a option \<Rightarrow> 'a" 
  where [simp add]: "opt_get optval \<equiv> (THE v . optval = Some v)"

definition map_get :: "('a, 'b) map \<Rightarrow> 'a \<Rightarrow> 'b"  (infixl "$" 73)
  where [simp add]: "map_get m k = opt_get (m k)"

lemma map_some_val: 
  assumes "x \<in> dom f"
  shows "(f x = Some y) = (f $ x = y)"
proof
  show "f x = Some y \<Longrightarrow> f $ x = y"
    by simp
next
  show "f $ x = y \<Longrightarrow> f x = Some y"
    using assms by force
qed

lemma map_some_val_given:
  assumes "f x = Some y"
  shows "f $ x = y"
  by (simp add: assms)

lemma singleton_unfold: "[a \<mapsto> b] = (\<lambda>x. if x = a then Some b else None)"
  by fastforce

lemma singleton_map_upd: "m(a\<mapsto>b) = m ++ [a \<mapsto> b]"
  unfolding map_add_def singleton_unfold
  by fastforce

definition map_Add (infixl "**" 100) where "map_Add X Y = {x ++ y | x y. x \<in> X \<and> y \<in> Y }"

lemma map_Add_assoc: "X ** (Y ** Z) = (X ** Y) ** Z"
proof
  show "X ** Y ** Z \<subseteq> X ** (Y ** Z)" 
  proof
    fix x
    assume "x \<in> X ** Y ** Z"
    then show "x \<in> X ** (Y ** Z)" unfolding map_Add_def apply simp
      by (metis map_add_assoc)
    qed
next
  show "X ** (Y ** Z) \<subseteq> X ** Y ** Z" unfolding map_Add_def apply simp by force
qed

lemma map_Add_empty_right: "X ** {} = {}" unfolding map_Add_def by simp
lemma map_Add_empty_left: "{} ** X = {}" unfolding map_Add_def by simp

lemma map_Add_extract: "{s ++ m | s m. s \<in> S \<and> p m } = S ** { m | m. p m }"
proof
  show "{s ++ m |s m. s \<in> S \<and> p m} \<subseteq> S ** {m |m. p m}" using map_Add_def by fastforce
next
  show "S ** {m |m. p m} \<subseteq> {s ++ m |s m. s \<in> S \<and> p m}" by (simp add: map_Add_def)
qed

definition merge :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixl "\<uplus>\<^sub>m" 55) where
  "m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<equiv> \<lambda>a. if \<exists>y. {Some y} = {m\<^sub>1 a, m\<^sub>2 a} - {None} then (THE b. b \<in> {m\<^sub>1 a, m\<^sub>2 a} - {None}) else None"

lemma merge_unit[simp]: "m \<uplus>\<^sub>m Map.empty = m"
proof
  fix x
  show "(m \<uplus>\<^sub>m Map.empty) x = m x"
    proof (cases "m x = None")
      case True
      then show ?thesis 
        by (simp add: merge_def)
    next
      case False
      then show ?thesis
        apply (simp add: merge_def)
        by auto
    qed
qed

lemma merge_comm: "m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 = m\<^sub>2 \<uplus>\<^sub>m m\<^sub>1"
proof
  fix x
  show "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) x = (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>1) x"
  proof (cases "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) x = None")
    case True
    then show ?thesis 
      by (smt (verit) insertI1 insert_commute merge_def singletonD the_equality)
  next
    case False
    then show ?thesis
      by (simp add: insert_commute merge_def)
  qed
qed

(*  Syntax error related to subscripts in the text below.
text \<open> Associativity "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) \<uplus>\<^sub>m m\<^sub>3 = m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)" does not hold in general because None models top and bottom \<close>
*)

lemma assoc_disjoint:
  assumes d1: "dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
      and d2: "dom m\<^sub>1 \<inter> dom m\<^sub>3 = {}"
      and d3: "dom m\<^sub>2 \<inter> dom m\<^sub>3 = {}"
    shows "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) \<uplus>\<^sub>m m\<^sub>3 = m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)"
proof -
  have h1: "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) \<uplus>\<^sub>m m\<^sub>3 \<subseteq>\<^sub>m m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)"
  proof (simp only: map_le_def; standard)
    fix a
    assume "a \<in> dom (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)"
    then obtain y where y1: "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) a = Some y" by blast
    hence h4: "Some y = (m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)) a"
    proof (cases "a \<in> dom m\<^sub>1")
      case True
      have u1: "m\<^sub>1 a = Some y"
        using y1 True d1 apply (simp add: merge_def)
        by (smt (z3) Diff_iff d2 domIff insert_absorb insert_disjoint(2) insert_iff option.distinct(1) the1_equality)
      then show ?thesis 
        using True d1 d2 apply (simp add: merge_def)
        by (smt (verit) Diff_insert_absorb domIff insertE insert_absorb insert_absorb2 insert_commute insert_disjoint(2) insert_not_empty option.distinct(1) the_equality)
    next
      case False
      have u2: "m\<^sub>1 a = None" using False by blast
      then show ?thesis
      proof (cases "a \<in> dom m\<^sub>2")
        case True
        have u1: "m\<^sub>2 a = Some y"
          using y1 True d2 apply (simp add: merge_def)
          by (smt (z3) Diff_iff d3 domIff insert_absorb insert_disjoint(1) insert_iff option.distinct(1) the1_equality)
        have u3: "m\<^sub>3 a = None" using True d3 by blast
      then show ?thesis
        using True u1 u2 u3 apply (simp add: merge_def)
        by (smt (verit, best) Diff_cancel empty_Diff insert_Diff_if member_remove not_None_eq remove_def the_equality)
      next
        case False
        have u3: "m\<^sub>2 a = None" using False by blast
        have u1: "m\<^sub>3 a = Some y"
          using y1 u2 u3 apply (simp add: merge_def)
          by (smt (z3) Diff_cancel Diff_insert_absorb insert_absorb2 insert_not_empty option.simps(3) singletonD theI_unique)
        then show ?thesis using False u1 u2 u3 by (simp add: merge_def)
      qed
    qed
    show "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) a = (m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)) a" by (simp add: h4 y1)
  qed
  have h2: "m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) \<subseteq>\<^sub>m (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) \<uplus>\<^sub>m m\<^sub>3" 
  proof (simp only: map_le_def; standard)
    fix a
    assume a1: "a \<in> dom (m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3))"
    then obtain y where y1: "(m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)) a = Some y" by blast
    hence h5: " Some y = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) a"
    proof (cases "a \<in> dom m\<^sub>1")
      case True
      have u1: "m\<^sub>1 a = Some y"
        using y1 True apply (simp add: merge_def)
        by (smt (z3) Diff_iff a1 domIff insertCI insertE the_equality y1)
      have u2: "m\<^sub>2 a = None" using True d1 by blast
      have u3: "m\<^sub>3 a = None" using True d2 by blast
      then show ?thesis
        using True u1 u2 u3 y1 apply (simp add: merge_def)
        by (smt (verit) option.distinct(1) the_equality)
    next
      case False
      have u2: "m\<^sub>1 a = None" using False by blast
      then show ?thesis
      proof (cases "a \<in> dom m\<^sub>2")
        case True
        have u1: "m\<^sub>2 a = Some y"
          using y1 u2 True d2 apply (simp add: merge_def)
          by (smt (z3) Diff_iff domIff insert_iff option.simps(3) theI)
        have u3: "m\<^sub>3 a = None" using True d3 by blast
        then show ?thesis
          using u1 u2 u3 apply (simp add: merge_def)
          by (smt (verit, best) Diff_insert_absorb emptyE insertE insert_commute option.distinct(1) the_equality)
      next
        case False
        have u1: "m\<^sub>2 a = None" using False by blast
        have u3: "m\<^sub>3 a = Some y"
          using y1 u2 u1 apply (simp add: merge_def)
          by (smt (z3) Diff_iff insert_Diff1 option.distinct(1) singletonD singletonI theI)
        then show ?thesis using False u1 u2 u3 by (simp add: merge_def)
      qed
    qed
    show "(m\<^sub>1 \<uplus>\<^sub>m (m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3)) a = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<uplus>\<^sub>m m\<^sub>3) a" by (simp add: h5 y1)
  qed
  show ?thesis using h1 h2 map_le_antisym by blast
qed

definition Merge :: "('a \<rightharpoonup> 'b) set \<Rightarrow> ('a \<rightharpoonup> 'b)"  ("\<Uplus>\<^sub>m _" [900] 900) where
  "(\<Uplus>\<^sub>m M) \<equiv> \<lambda>a. if (\<exists>y. {Some y} = { b | b m. m \<in> M \<and> m a = b  \<and> b \<noteq> None }) 
    then (THE b. \<exists> m. m \<in> M \<and> m a = b \<and> b \<noteq> None) 
    else None"

lemma Merge_empty[simp]: "(\<Uplus>\<^sub>m {}) = Map.empty"
  unfolding Merge_def by simp

lemma map_Merge_not_none: "(\<Uplus>\<^sub>m M) a \<noteq> None \<Longrightarrow> \<exists>y. \<forall>m \<in> M. m a \<noteq> None \<longrightarrow> m a = Some y"
proof -
  assume a1: "(\<Uplus>\<^sub>m M) a \<noteq> None"
  then obtain y where y1: "(\<Uplus>\<^sub>m M) a = Some y" by blast
  hence h1: "Some y = (THE b. \<exists> m. m \<in> M \<and> m a = b \<and> b \<noteq> None)"
    by (metis (mono_tags, lifting) Merge_def option.distinct(1))
  have "\<forall>m \<in> M. m a \<noteq> None \<longrightarrow> m a = Some y"
  proof
    fix m
    assume m1: "m \<in> M"
    show "m a \<noteq> None \<longrightarrow> m a = Some y"
    proof
      assume m2: "m a \<noteq> None"
      show "m a = Some y" using a1 m1 m2 apply(simp add: h1 Merge_def)
        by (smt (verit, del_insts) mem_Collect_eq option.distinct(1) singleton_iff theI_unique)
    qed
  qed
  thus ?thesis by blast
qed

lemma map_Merge_le: "\<lbrakk>m \<in> M; \<forall>m' \<in> M. dom m \<inter> dom m' = {}\<rbrakk> \<Longrightarrow> (\<Uplus>\<^sub>m M) |` dom m \<subseteq>\<^sub>m m"
  by fastforce

lemma map_Merge_dom: 
  assumes "\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
  shows "dom (\<Uplus>\<^sub>m M) = (\<Union>m \<in> M. dom m)"
proof
  show "dom (\<Uplus>\<^sub>m M) \<subseteq> (\<Union>m \<in> M. dom m)"
  proof
    fix x
    assume "x \<in> dom (\<Uplus>\<^sub>m M)"
    then show "x \<in> (\<Union>m \<in> M. dom m)"
      unfolding dom_def apply(simp add: Merge_def)
      by (smt (verit) insertI1 mem_Collect_eq option.distinct(1))
  qed
next
  show "(\<Union>m \<in> M. dom m) \<subseteq> dom (\<Uplus>\<^sub>m M)"
  proof
    fix x
    assume "x \<in> (\<Union>m \<in> M. dom m)"
    then show "x \<in> dom (\<Uplus>\<^sub>m M)"
      unfolding dom_def apply(simp add: Merge_def)
      using assms by fastforce
  qed
qed

lemma not_dom_Merge: 
  assumes a: "a \<notin> M"
      and d: "\<forall>m \<in> M. dom a \<inter> dom m = {}"
    shows "dom a \<inter> dom (\<Uplus>\<^sub>m M) = {}"
proof
  have "\<And>x. x \<in> dom a \<Longrightarrow> x \<notin> dom (\<Uplus>\<^sub>m M)"
    using a d unfolding Merge_def apply (simp add: dom_def; clarify)
    by (smt (verit) domI empty_Collect_eq insert_disjoint(2) insert_dom insert_not_empty)
  thus "dom a \<inter> dom (\<Uplus>\<^sub>m M) \<subseteq> {}" by blast
next
  show "{} \<subseteq> dom a \<inter> dom (\<Uplus>\<^sub>m M)" by blast
qed

lemma empty_Merge: 
  assumes a: "a = Map.empty"
    shows "dom a \<inter> dom (\<Uplus>\<^sub>m M) = {}"
  by (simp add: assms)

lemma merge_Merge_union: 
  assumes d: "\<forall>m' \<in> M. dom m \<inter> dom m' = {}"
  shows "\<Uplus>\<^sub>m (M\<union>{m}) = \<Uplus>\<^sub>m M \<uplus>\<^sub>m m"
proof (rule map_le_antisym)
  show h1: "(\<Uplus>\<^sub>m (M \<union> {m})) \<subseteq>\<^sub>m (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m)"
  proof (simp only: map_le_def; standard)
    fix a
    assume a1: "a \<in> dom (\<Uplus>\<^sub>m (M \<union> {m}))"
    then obtain y where a2: "Some y = (\<Uplus>\<^sub>m (M \<union> {m})) a" by force
    have "Some y = (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) a"
    proof (cases "a \<in> dom m")
      case True
      then have t1: "a \<in> dom m" by blast
      then have a3: "Some y = m a" using a2 unfolding Merge_def
        by (metis (mono_tags, lifting) UnI2 domIff mem_Collect_eq option.simps(3) 
            singletonD singletonI the_equality)
      show ?thesis
      proof (cases "a \<in> dom (\<Uplus>\<^sub>m M)")
        case True
        have "(\<Uplus>\<^sub>m M) a = Some y"
          using t1 True d unfolding Merge_def apply (simp only: a2 a3)
          by (smt (verit) domIff empty_Collect_eq insert_absorb insert_disjoint(2) insert_not_empty)
        then show ?thesis using t1 d a3 unfolding Merge_def
          by (smt (verit, best) domIff insert_disjoint(1) insert_dom mem_Collect_eq singletonI)
      next
        case False
        then have t2: "(\<Uplus>\<^sub>m M) a = None" by (simp add: domIff)
        show ?thesis using False t1 d a3 unfolding merge_def apply (simp add: t2)
          by (smt (verit, ccfv_threshold) Diff_empty Diff_insert0 emptyE insertE the_equality)
      qed
    next
      case False
      hence t4: "m a = None" by blast
      hence t5: "\<forall>m' \<in> M. m' a = Some y \<or> m' a = None" 
        using a2 t4 unfolding Merge_def
        by (metis (mono_tags, lifting) Un_iff mem_Collect_eq option.simps(3) singleton_iff the_equality)
      then obtain m' where t6: "m' \<in> M" and t7: "m' a = Some y"
        using a1 unfolding Merge_def
        by (smt (verit, ccfv_threshold) False Un_iff domIff empty_Collect_eq insert_not_empty singletonD)
      hence t5: "(\<Uplus>\<^sub>m M) a = Some y" using t5 unfolding Merge_def apply simp
        by (smt (verit, ccfv_threshold) Collect_cong option.distinct(1) singleton_conv the_equality)
      then show ?thesis using t5 unfolding merge_def
        by (simp add: insert_commute t4)
    qed
    then show "(\<Uplus>\<^sub>m (M \<union> {m})) a = (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) a" by (simp add: a2)
  qed
next
  show h2: "(\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) \<subseteq>\<^sub>m (\<Uplus>\<^sub>m (M \<union> {m}))"
  proof (simp only: map_le_def; standard)
    fix a
    assume a3: "a \<in> dom (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m)"
    then obtain y where b1: "Some y = (\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) a" by force
    have b2: "Some y = (\<Uplus>\<^sub>m (M \<union> {m})) a"
    proof (cases "a \<in> dom m")
      case True
      hence b3: "m a = Some y" using b1 unfolding merge_def
        by (smt (z3) Diff_iff domIff empty_Collect_eq insert_Diff1 insert_Diff_single insert_absorb 
            insert_commute insert_iff insert_not_empty merge_def not_Some_eq singletonD singletonI theI)
      hence b5: "\<forall>m' \<in> M. m' a = Some y \<or> m' a = None"
        using True d by blast
      hence b6: "\<forall>m' \<in> M\<union>{m}. m' a = Some y \<or> m' a = None" using b3 by fastforce
      then show ?thesis unfolding Merge_def
        by (smt (z3) Collect_cong True Un_insert_right domIff insert_iff singleton_conv2 the_equality)
    next
      case False
      hence b7: "m a = None" by blast
      hence b8: "Some y = (\<Uplus>\<^sub>m M) a" using b1 unfolding merge_def
        by (metis Diff_iff insertI1 insert_absorb2 option.distinct(1) singletonD the_equality)
      hence b9: "\<forall>m' \<in> M. m' a = Some y \<or> m' a = None" unfolding Merge_def 
        by (metis (mono_tags, lifting) mem_Collect_eq option.simps(3) singleton_iff the_equality)
      hence t8: "\<forall>m' \<in> M\<union>{m}. m' a = Some y \<or> m' a = None" using b7 by simp
      from b8 b9 obtain m' where x1: "m' \<in> M" and x2: "m' a = Some y" unfolding Merge_def
        by (smt (verit, best) all_not_in_conv empty_not_insert mem_Collect_eq option.distinct(1))
      then show ?thesis using t8 unfolding Merge_def
        by (smt (z3) Collect_cong Collect_empty_eq UnCI singleton_conv the_equality)
    qed
    show "(\<Uplus>\<^sub>m M \<uplus>\<^sub>m m) a = (\<Uplus>\<^sub>m (M \<union> {m})) a"
      using b1 b2 by presburger
  qed
qed

lemma merge_Merge_diff: 
  assumes m: "m \<in> M"
      and d: "\<forall>m' \<in> M-{m}. dom m \<inter> dom m' = {}"
  shows "\<Uplus>\<^sub>m M = \<Uplus>\<^sub>m (M-{m}) \<uplus>\<^sub>m m"
  using d m merge_Merge_union[of "M-{m}" "m"] by (simp add: insert_absorb)

lemma map_add_merge:
  assumes d: "dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
  shows "m\<^sub>1 ++ m\<^sub>2 = m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2"
proof (rule map_le_antisym)
  show "m\<^sub>1 ++ m\<^sub>2 \<subseteq>\<^sub>m m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2"
  proof (simp only: map_le_def; standard)
    fix a
    assume a1: "a \<in> dom (m\<^sub>1 ++ m\<^sub>2)"
    then obtain y where y1: "Some y = (m\<^sub>1 ++ m\<^sub>2) a" by (metis domD)
    hence "Some y = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a"
    proof (cases "a \<in> dom m\<^sub>1")
      case True
      hence b0: "m\<^sub>2 a = None" using d by blast
      hence b1: "(m\<^sub>1 ++ m\<^sub>2) a = m\<^sub>1 a" using d by (simp add: domIff map_add_dom_app_simps(3))
      then show ?thesis using b0 y1 unfolding merge_def apply (simp add: b1)
        by (smt (verit, ccfv_SIG) Diff_insert_absorb empty_iff insertE insert_commute 
            option.distinct(1) the_equality)
    next
      case False
      hence b2: "(m\<^sub>1 ++ m\<^sub>2) a = m\<^sub>2 a" using d by (simp add: map_add_dom_app_simps(2))
      then show ?thesis using False y1 unfolding merge_def apply (simp add: b2)
        by (smt (verit, ccfv_threshold) Diff_insert_absorb domIff empty_iff insert_iff 
            option.distinct(1) the_equality)
    qed
    then show "(m\<^sub>1 ++ m\<^sub>2) a = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a" using y1 by presburger
  qed
next
  show "m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2 \<subseteq>\<^sub>m m\<^sub>1 ++ m\<^sub>2"
  proof (simp only: map_le_def; standard)
    fix a
    assume a2: "a \<in> dom (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2)"
    then obtain y where y1: "Some y = (m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a" by (metis domD)
    hence "Some y = (m\<^sub>1 ++ m\<^sub>2) a"
    proof (cases "a \<in> dom m\<^sub>1")
      case True
      hence b3: "m\<^sub>2 a = None" using d by blast
      have b4: "m\<^sub>1 a = Some y" using y1 True d unfolding merge_def apply (simp only: b3)
        by (metis (no_types, lifting) Diff_iff insertE option.distinct(1) singletonI the_equality)
      then show ?thesis by (simp add: b3 map_add_def)
    next
      case False
      hence b5: "m\<^sub>1 a = None" by blast
      have b6: "m\<^sub>2 a = Some y" using y1 False d unfolding merge_def apply (simp only: b5)
        by (metis Diff_iff insertCI insertE not_None_eq theI)
      then show ?thesis by simp
    qed
    then show "(m\<^sub>1 \<uplus>\<^sub>m m\<^sub>2) a = (m\<^sub>1 ++ m\<^sub>2) a" using y1 by presburger
  qed
qed

fun map_add_seq where
  "map_add_seq s [] = s"
| "map_add_seq s (m#ms) = map_add_seq (s ++ m) ms"

lemma map_add_seq_foldl: "map_add_seq s ms = foldl map_add s ms"
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by fastforce
next
  case (Cons a ms)
  then show ?case by simp
qed

lemma map_add_seq_Merge_eq: 
  "\<lbrakk> \<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. m\<^sub>1 \<noteq> m\<^sub>2 \<longrightarrow> dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}; M = set ms; card M = length ms \<rbrakk> \<Longrightarrow> map_add_seq s ms = s ++ (\<Uplus>\<^sub>m M)"
proof (induction ms arbitrary: M s)
  case Nil
  have h1: "map_add_seq s [] = s" by simp
  hence h2: "M = {}" using Nil.prems(2) by auto  
  hence h2: "\<Uplus>\<^sub>m M = Map.empty" by simp
  then show ?case by simp
next
  case (Cons a ms)
  have h3: "a \<notin> set ms" by (metis Cons.prems(2) Cons.prems(3) card_distinct distinct.simps(2))
  have h4: "M = {a} \<union> set ms" by (simp add: Cons.prems(2))
  have h5: "card (M-{a}) = length ms" using h3 apply (simp add: h4)
    using Cons.prems(2) Cons.prems(3) by auto
  have x2: "\<forall>m \<in> M. a \<noteq> m \<longrightarrow> dom a \<inter> dom m = {}" by (simp add: Cons.prems(1) h4)
  have x3: "dom a \<inter> dom (\<Uplus>\<^sub>m (M - {a})) = {}"
     by (metis DiffD1 DiffD2 insertI1 not_dom_Merge x2)
  have h6: "map_add_seq (s ++ a) ms = (s ++ a) ++ \<Uplus>\<^sub>m (M-{a})"
    using Cons.IH[of "M-{a}" "s ++ a"] 
    using Cons.prems(1) h3 h4 h5 by force
  have h7: "map_add_seq s (a#ms) = (s ++ a) ++ \<Uplus>\<^sub>m (M-{a})"
    using Cons.prems(1) Cons.prems(2) h6 by simp
  have h8: "... = s ++ (a ++ \<Uplus>\<^sub>m (M-{a}))" by simp
  have h9: "... = s ++ (a \<uplus>\<^sub>m \<Uplus>\<^sub>m (M-{a}))" using map_add_merge[of a "\<Uplus>\<^sub>m (M - {a})"]
    using Cons.prems(1) Cons.prems(2) x3 by fastforce
  have x1: "... = s ++ (\<Uplus>\<^sub>m M)" using x2 merge_Merge_diff[of a M]
    by (metis Cons.prems(2) DiffD1 DiffD2 insertI1 list.set_intros(1) merge_comm)
  then show ?case using h7 h8 h9 x1 by presburger
qed

lemma seq_set_dom:
  "\<forall>i j. i \<le> length ms \<and> j \<le> length ms \<and> i \<noteq> j \<longrightarrow> dom (ms!i) \<inter> dom (ms!j) = {} \<Longrightarrow> 
  \<forall>m\<^sub>1 \<in> set ms.\<forall>m\<^sub>2 \<in> set ms. m\<^sub>1 \<noteq> m\<^sub>2 \<longrightarrow> dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
proof (induction ms)
  case Nil
  then show ?case by auto
next
  case (Cons a ms)
  then show ?case by (metis in_set_conv_nth less_le)
qed

lemma map_add_seq_Merge: 
  "\<lbrakk> \<forall>i j. i \<le> length ms \<and> j \<le> length ms \<and> i \<noteq> j \<longrightarrow> dom (ms!i) \<inter> dom (ms!j) = {}; 
    card (set ms) \<le> length ms \<rbrakk> \<Longrightarrow> map_add_seq s ms = s ++ (\<Uplus>\<^sub>m set ms)"
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a ms)
  have h0: "\<forall>k. k \<le> length ms \<longrightarrow> ms ! k = (a # ms) ! (Suc k)" by simp
  have h1: "\<forall>i j. i \<le> length ms \<and> j \<le> length ms \<and> i \<noteq> j \<longrightarrow> dom (ms ! i) \<inter> dom (ms ! j) = {}"
  proof (clarify)
    fix i j
    assume a1: "i \<le> length ms"
       and a2: "j \<le> length ms"
       and a3: "i \<noteq> j"
    then show "dom (ms ! i) \<inter> dom (ms ! j) = {}"
      by (metis Cons.prems(1) Suc_inject h0 a1 a2 a3 length_Cons not_less_eq_eq)
  qed
  have h2: "\<forall>m \<in> set ms. a \<noteq> m \<longrightarrow> dom a \<inter> dom m = {}" 
    by (meson Cons.prems(1) list.set_intros(1) list.set_intros(2) seq_set_dom)
  have h3: "a \<noteq> Map.empty \<Longrightarrow> a \<notin> set ms"
  proof -
    assume a4: "a \<noteq> Map.empty"
    hence a5: "dom a \<noteq> {}" by simp
    thus "a \<notin> set ms" using h0 Cons.prems(1)
      by (metis Suc_le_mono in_set_conv_nth inf.idem length_Cons less_imp_le_nat 
          nat.simps(3) nth_Cons_0 zero_le)
  qed
  have h3: "dom a \<inter> dom (\<Uplus>\<^sub>m set ms) = {}"
    using h2 h3 not_dom_Merge by fastforce
  have h4: "map_add_seq (s ++ a) ms = (s ++ a) ++ \<Uplus>\<^sub>m set ms" using Cons.IH card_length h1 by blast
  have h5: "... = s ++ (a ++ \<Uplus>\<^sub>m set ms)" by simp
  have h6: "... = s ++ (a \<uplus>\<^sub>m \<Uplus>\<^sub>m set ms)" using map_add_merge[of a "\<Uplus>\<^sub>m set ms"] by (simp add: h3)
  have h7: "... = s ++ (\<Uplus>\<^sub>m (set ms \<union> {a}))" 
    using h2 h3 map_add_merge not_dom_Merge merge_Merge_union[of "set ms" a]
    by (smt (verit) DiffD1 DiffD2 DiffI Diff_empty Diff_insert_absorb Int_commute 
        Int_empty_right Un_empty_right disjoint_iff_not_equal domIff insert_Diff insert_Diff_single 
        map_add_dom_app_simps(1) merge_Merge_diff merge_comm mk_disjoint_insert)
  then show ?case by (metis h4 h5 h6 insert_is_Un list.simps(15) map_add_seq.simps(2) sup_commute)
qed

fun map_Add_seq where
  "map_Add_seq S [] = S"
| "map_Add_seq S (M#Ms) = map_Add_seq (S ** M) Ms"

lemma map_Add_seq_foldl: "map_Add_seq S Ms = foldl map_Add S Ms"
proof (induction Ms arbitrary: S)
  case Nil
  then show ?case by fastforce
next
  case (Cons a ms)
  then show ?case by simp
qed

fun map_seq_in where
  "map_seq_in [] [] = True"
| "map_seq_in (x#xs) (X#XS) = (x \<in> X \<and> map_seq_in xs XS)"
| "map_seq_in _ _ = False"

lemma map_seq_in_ex: "\<lbrakk> m \<in> set ms; map_seq_in ms Ms \<rbrakk> \<Longrightarrow> \<exists>M \<in> set Ms. m \<in> M"
proof (induction Ms arbitrary: ms)
  case Nil
  then show ?case using map_seq_in.elims(2) by force
next
  case (Cons a ms)
  then show ?case by (metis list.set_cases list.set_intros(1) list.set_intros(2) map_seq_in.simps(2))
qed

lemma map_seq_in_in: 
  "\<lbrakk>\<forall>i j. i \<le> length ms \<and> j \<le> length ms \<and> i \<noteq> j \<longrightarrow> dom (ms!i) \<inter> dom (ms!j) = {};
    \<forall>M \<in> set Ms.\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 = dom m\<^sub>2;
    card (set ms) \<le> length ms; 
    map_seq_in ms Ms;
    m\<^sub>1 \<in> set ms;
    m\<^sub>2 \<in> set ms;
    m\<^sub>1 \<noteq> m\<^sub>2 \<rbrakk> \<Longrightarrow> \<exists>M\<^sub>1 \<in> set Ms.\<exists>M\<^sub>2 \<in> set Ms. M\<^sub>1 \<noteq> M\<^sub>2 \<and> m\<^sub>1 \<in> M\<^sub>1 \<and> m\<^sub>2 \<in> M\<^sub>2"
proof (induction Ms arbitrary: ms)
  case Nil
  then show ?case
    by (metis empty_iff list.collapse map_seq_in.simps(3) set_empty)
next
  case (Cons a Ms)
  have h0: "\<forall>k. k \<le> length (tl ms) \<longrightarrow> (tl ms) ! k = ms ! (Suc k)"
    by (metis length_greater_0_conv length_pos_if_in_set list.collapse local.Cons(6) nth_Cons_Suc)
  then have h1: "\<forall>i j. i \<le> length (tl ms) \<and> j \<le> length (tl ms) \<and> i \<noteq> j \<longrightarrow> dom ((tl ms)!i) \<inter> dom ((tl ms)!j) = {}"
    by (metis Cons.prems(1) Cons.prems(5) Nitpick.size_list_simp(2) Suc_le_mono 
        length_greater_0_conv length_pos_if_in_set old.nat.inject)
  have h2: "\<forall>M\<in>set Ms. \<forall>m\<^sub>1\<in>M. \<forall>m\<^sub>2\<in>M. dom m\<^sub>1 = dom m\<^sub>2" by (meson Cons.prems(2) list.set_intros(2))
  have h3: "card (set (tl ms)) \<le> length (tl ms)" using card_length by blast
  have h4: "map_seq_in (tl ms) Ms" using Cons.prems(4) map_seq_in.elims(2) by fastforce
  have h5: "m\<^sub>1 \<noteq> m\<^sub>2" by (simp add: Cons.prems(7))
  then show ?case
  proof (cases "m\<^sub>1 \<in> set (tl ms)")
    case True
    hence h6: "m\<^sub>1 \<in> set (tl ms)" by simp
    then show ?thesis
    proof (cases "m\<^sub>2 \<in> set (tl ms)")
      case True
      hence h7: "m\<^sub>2 \<in> set (tl ms)" by simp
      have "\<exists>M\<^sub>1\<in>set Ms. \<exists>M\<^sub>2\<in>set Ms. M\<^sub>1 \<noteq> M\<^sub>2 \<and> m\<^sub>1 \<in> M\<^sub>1 \<and> m\<^sub>2 \<in> M\<^sub>2"
        using Cons.IH Cons.prems(7) h1 h2 h3 h4 h6 h7 by presburger
      then show ?thesis by (meson list.set_intros(2))
    next
      case False
      hence h7: "m\<^sub>2 \<notin> set (tl ms)" by simp
      hence x1: "m\<^sub>2 \<in> a" 
        using Cons.prems(4) Cons.prems(6) equals0D map_seq_in.elims(2) set_ConsD by force
      obtain M where "m\<^sub>1 \<in> M" and "M \<in> set Ms" by (meson h4 h6 map_seq_in_ex)
      then show ?thesis
        sorry
        (*
        using h2 h5 x1 seq_set_dom
        by (smt (verit, ccfv_threshold) Cons.prems(1) Cons.prems(5) Cons.prems(6) dom_eq_empty_conv 
            inf.idem list.set_intros(1) list.set_intros(2)) *)
    qed
  next
    case False
    hence h6: "m\<^sub>1 \<notin> set (tl ms)" by simp
    hence x1: "m\<^sub>1 \<in> a" using Cons.prems(4) Cons.prems(5) list.set_cases by force
    then show ?thesis
    proof (cases "m\<^sub>2 \<in> set (tl ms)")
      case True
      hence h7: "m\<^sub>2 \<in> set (tl ms)" by simp
      then show ?thesis
        sorry 
        (*
        by (smt (verit, best) Cons.prems(1) Cons.prems(2) Cons.prems(4) Cons.prems(5) Cons.prems(6) 
            dom_eq_empty_conv h5 inf.idem map_seq_in_ex seq_set_dom) *)
    next
      case False
      then show ?thesis
        by (metis Cons.prems(5) Cons.prems(6) h5 h6 hd_Cons_tl length_greater_0_conv 
            length_pos_if_in_set set_ConsD)
    qed
  qed
qed


lemma map_Add_seq_as_add_seq: 
  "map_Add_seq S Ms = {map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms Ms}"
proof (induction Ms arbitrary: S)
  case Nil
  then show ?case
  proof
    show "map_Add_seq S [] \<subseteq> {map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms []}"
    proof
      fix x
      assume "x \<in> map_Add_seq S []"
      then show "x \<in> {map_add_seq s ms |s ms. s \<in> S \<and> map_seq_in ms []}"
        apply simp
        by (metis map_add_seq.simps(1) map_seq_in.simps(1))
    qed
  next
    show "{map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms []} \<subseteq> map_Add_seq S []"
    proof
      fix x
      assume "x \<in> {map_add_seq s ms |s ms. s \<in> S \<and> map_seq_in ms []}"
      then show "x \<in> map_Add_seq S []"
        apply simp
        using map_seq_in.elims(1) by force
    qed
  qed
next
  case (Cons A Ms)
  have h1: "map_Add_seq (S ** A) Ms = {map_add_seq s ms | s ms. s \<in> (S ** A) \<and> map_seq_in ms Ms}"
    using local.Cons by blast
  show ?case
  proof
    show "map_Add_seq S (A#Ms) \<subseteq> {map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms (A#Ms)}"
    proof
      fix x
      assume a1: "x \<in> map_Add_seq S (A # Ms)"
      hence a2: "x \<in> map_Add_seq (S ** A) Ms" by simp
      obtain s a ms where p1: "s \<in> S" and
                          p2: "a \<in> A" and
                          p3: "map_seq_in ms Ms" and 
                          p4: "x = map_add_seq (s ++ a) ms"
        by (smt (verit, ccfv_SIG) a2 h1 map_Add_def mem_Collect_eq)
      have a3: "map_seq_in (a#ms) (A#Ms)" by (simp add: p2 p3)
      then show "x \<in> {map_add_seq s ms |s ms. s \<in> S \<and> map_seq_in ms (A # Ms)}"
        by (smt (verit) map_add_seq.simps(2) mem_Collect_eq p1 p4)
    qed
  next
    show "{map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms (A#Ms)} \<subseteq> map_Add_seq S (A#Ms)"
    proof
      fix x
      assume a4: "x \<in> {map_add_seq s ms |s ms. s \<in> S \<and> map_seq_in ms (A # Ms)}"
      then obtain s a ms where q1: "s \<in> S" and
                               q2: "a \<in> A" and
                               q3: "map_seq_in ms Ms" and
                               q4: "x = map_add_seq s (a#ms)" 
        by (smt (verit, del_insts) CollectD list.discI list.sel(1) list.sel(3) map_seq_in.elims(2))
      show "x \<in> map_Add_seq S (A # Ms)" 
        using h1 map_Add_def q1 q2 q3 q4 by fastforce
    qed
  qed
qed

lemma map_Add_seq_Merge: 
  "\<lbrakk> \<forall>i j. i \<le> length ms \<and> j \<le> length ms \<and> i \<noteq> j \<longrightarrow> dom (ms!i) \<inter> dom (ms!j) = {}; 
  \<forall>M \<in> set Ms.\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 = dom m\<^sub>2; card (set Ms) \<le> length Ms \<rbrakk> \<Longrightarrow> 
  map_Add_seq S Ms = S ** {\<Uplus>\<^sub>m set ms | ms. map_seq_in ms Ms}"
proof (induction Ms arbitrary: ms)
  case Nil
  show ?case
  proof
    show h1: "map_Add_seq S [] \<subseteq> S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms []}"
      unfolding map_Add_def apply (simp; clarify)
      by (metis Suc_leI bot_nat_0.not_eq_extremum card_length list.size(3) map_add_seq.simps(1) 
          map_add_seq_Merge map_seq_in.simps(1) not_less_eq_eq)
  next
    show h2: "S ** {\<Uplus>\<^sub>m set ms |ms. map_seq_in ms []} \<subseteq> map_Add_seq S []"
      unfolding map_Add_def apply (simp; clarify) 
      by (metis card.empty emptyE empty_set list.size(3) map_add_seq.simps(1) map_add_seq_Merge_eq 
          map_seq_in.simps(3) neq_Nil_conv)
  qed
next
  case (Cons a Ms)
  then show ?case sorry
qed

(*proof -
  have h0: "\<forall>M\<^sub>1 \<in> M.\<forall>M\<^sub>2 \<in> M. M\<^sub>1 \<noteq> M\<^sub>2 \<longrightarrow> (\<forall>m\<^sub>1 \<in> M\<^sub>1.\<forall>m\<^sub>2 \<in> M\<^sub>2. m\<^sub>1 \<noteq> m\<^sub>2)"
    using n d by auto
  have h1: "map_Add_seq S Ms = {map_add_seq s ms | s ms. s \<in> S \<and> map_seq_in ms Ms}"
    by (simp add: map_Add_seq_as_add_seq)
  have h2: "... = {s ++ (\<Uplus>\<^sub>m set ms) | s ms. s \<in> S \<and> map_seq_in ms Ms}"
  proof -
    have "\<And>s ms. \<lbrakk>s \<in> S; map_seq_in ms Ms\<rbrakk> \<Longrightarrow> map_add_seq s ms = s ++ (\<Uplus>\<^sub>m set ms)"
    proof -
      fix s ms
      assume a1: "s \<in> S"
         and a2: "map_seq_in ms Ms"
      have x1: "\<forall>m\<^sub>1 \<in> set ms.\<forall>m\<^sub>2 \<in> set ms. m\<^sub>1 \<noteq> m\<^sub>2 \<longrightarrow> dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
      proof (clarify)
        fix m\<^sub>1 m\<^sub>2
        assume a3: "m\<^sub>1 \<in> set ms"
           and a4: "m\<^sub>2 \<in> set ms"
           and a5: "m\<^sub>1 \<noteq> m\<^sub>2"
        obtain M\<^sub>1 M\<^sub>2 where m1: "M\<^sub>1 \<in> M" and
                           m2: "M\<^sub>2 \<in> M" and
                           m3: "M\<^sub>1 \<noteq> M\<^sub>2" and
                           m4: "m\<^sub>1 \<in> M\<^sub>1" and
                           m5: "m\<^sub>2 \<in> M\<^sub>2" sorry
        show "dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}" sorry
      qed
      show "map_add_seq s ms = s ++ \<Uplus>\<^sub>m set ms" sorry
    qed
    then show ?thesis by force
  qed
  have h3: "... = {s ++ ms' | ms' s ms. s \<in> S \<and> ms' = \<Uplus>\<^sub>m set ms \<and> map_seq_in ms Ms}" by blast
  have h4: "... = S ** {ms' | ms' ms. ms' = \<Uplus>\<^sub>m set ms \<and> map_seq_in ms Ms}" 
    using map_Add_extract[of S "\<lambda>x. \<exists>s ms. x = \<Uplus>\<^sub>m set ms \<and> map_seq_in ms Ms"]
    apply simp by (smt (verit, best) Collect_cong)
  have h5: "... = S ** {\<Uplus>\<^sub>m set ms | ms. map_seq_in ms Ms}" by metis
  show ?thesis using h1 h2 h3 h4 by simp
qed

fun map_add_seq_pair where
  "map_add_seq_pair (s\<^sub>1, s\<^sub>2) [] = (s\<^sub>1, s\<^sub>2)"
| "map_add_seq_pair (s\<^sub>1, s\<^sub>2) ((m\<^sub>1, m\<^sub>2)#ms) = map_add_seq_pair (s\<^sub>1 ++ m\<^sub>1, s\<^sub>2 ++ m\<^sub>2) ms"

lemma map_add_seq_zip:
  "\<lbrakk>length ms = length ns; xs = zip ms ns \<rbrakk> \<Longrightarrow> map_add_seq_pair (s\<^sub>1, s\<^sub>2) xs = (map_add_seq s\<^sub>1 ms, map_add_seq s\<^sub>2 ns)"
proof (induction xs arbitrary: s\<^sub>1 s\<^sub>2 ms ns)
  case Nil
  then show ?case by force
next
  case (Cons a xs)
  then obtain a\<^sub>1 a\<^sub>2 where p1: "a = (a\<^sub>1, a\<^sub>2)" using old.prod.exhaust by blast
  obtain ms' where p2: "ms = a\<^sub>1#ms'" by (metis Cons.prems(2) p1 prod.inject zip_eq_ConsE)
  obtain ns' where p3: "ns = a\<^sub>2#ns'" by (metis Cons.prems(2) p1 prod.inject zip_eq_ConsE)
  have "map_add_seq_pair (s\<^sub>1, s\<^sub>2) (a#xs) = map_add_seq_pair (s\<^sub>1 ++ a\<^sub>1, s\<^sub>2 ++ a\<^sub>2) xs" by (simp add: p1)
  then show ?case using Cons.IH Cons.prems(1) Cons.prems(2) p2 p3 by force
qed

lemma map_add_seq_Merge_pair:
  assumes dM: "\<forall>m\<^sub>1 \<in> M.\<forall>m\<^sub>2 \<in> M. dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
      and dN: "\<forall>n\<^sub>1 \<in> N.\<forall>n\<^sub>2 \<in> N. dom n\<^sub>1 \<inter> dom n\<^sub>2 = {}"
      and sM: "M = set ms"
      and sN: "N = set ns"
      and cM: "card M = length ms"
      and cN: "card N = length ns"
      and cC: "card M = card N"
    shows "map_add_seq_pair (sm, sn) (zip ms ns) = (sm ++ (\<Uplus>\<^sub>m M), sn ++ (\<Uplus>\<^sub>m N))"
  using assms by (simp add: map_add_seq_Merge map_add_seq_zip)

lemma map_update_merge:
  assumes d: "a \<notin> dom m"
  shows "[a\<mapsto>b] ++ m = [a\<mapsto>b] \<uplus>\<^sub>m m"
  by (simp add: d map_add_merge)

fun map_upd_seq where 
  "map_upd_seq f s [] = s"
| "map_upd_seq f s (m#ms) = map_upd_seq f (s(m\<mapsto>f m)) ms"

lemma map_upd_seq_foldl: "map_upd_seq f s ms = foldl (\<lambda>s a. s(a\<mapsto>f a)) s ms"
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by fastforce
next
  case (Cons a ms)
  then show ?case by simp
qed

lemma map_upd_seq_add: "map_upd_seq f s ms = map_add_seq s (map (\<lambda>a. [a\<mapsto>f a]) ms)"
proof (induction ms arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons a ms)
  have "map_upd_seq f (s(a\<mapsto>f a)) ms = map_add_seq (s(a\<mapsto>f a)) (map (\<lambda>a. [a \<mapsto> f a]) ms)"
    using local.Cons by blast
  then show ?case unfolding map_upd_seq_foldl
    by (smt (verit, best) foldl_Cons list.distinct(1) list.inject list.simps(9) 
        map_add_seq.elims singleton_map_upd)
qed

lemma 
  assumes m: "X = set xs"
      and c: "card X = length xs"
    shows "map_upd_seq f s xs = s ++ (\<Uplus>\<^sub>m { [x \<mapsto> f x] | x. x \<in> X })"
proof -
  have h1: "\<forall>m\<^sub>1 \<in> { [x \<mapsto> f x] | x. x \<in> X }.\<forall>m\<^sub>2 \<in> { [x \<mapsto> f x] | x. x \<in> X }. m\<^sub>1 \<noteq> m\<^sub>2 \<longrightarrow> dom m\<^sub>1 \<inter> dom m\<^sub>2 = {}"
    apply (simp add: dom_def singleton_unfold)
    by force
  have h2: "X = set xs \<Longrightarrow> { [x \<mapsto> f x] | x. x \<in> X } = set (map (\<lambda>a. [a \<mapsto> f a]) xs)"
  proof (induction xs arbitrary: X)
    case Nil
    then show ?case by force
  next
    case (Cons a xs)
    then show ?case by auto
  qed
  have h3: "\<lbrakk> X = set xs; card X = length xs \<rbrakk> \<Longrightarrow> card { [x \<mapsto> f x] | x. x \<in> X } = length xs"
  proof (induction xs arbitrary: X)
    case Nil
    then show ?case by simp 
  next
    case (Cons a xs)
    hence a1: "X-{a} = set xs"
      by (metis Diff_insert_absorb card_distinct distinct.simps(2) list.simps(15))
    hence a2: "card (X-{a}) = length xs" 
      by (metis Cons.prems(1) Cons.prems(2) card_distinct distinct.simps(2) distinct_card)
    hence a3: "card { [x \<mapsto> f x] | x. x \<in> X-{a} } = length xs" using a1 by (simp add: Cons.IH)
    have a4: "[a \<mapsto> f a] \<notin> { [x \<mapsto> f x] | x. x \<in> X-{a} }"
      by (smt (verit, best) dom_eq_singleton_conv mem_Collect_eq member_remove remove_def)
    have a5: "{[x \<mapsto> f x] |x. x \<in> X} = {[a \<mapsto> f a]} \<union> { [x \<mapsto> f x] | x. x \<in> X-{a} }"
    proof
      show "{[a \<mapsto> f a]} \<union> {[x \<mapsto> f x] |x. x \<in> X - {a}} \<subseteq> {[x \<mapsto> f x] |x. x \<in> X}"
      proof
        fix x
        assume "x \<in> {[a \<mapsto> f a]} \<union> {[x \<mapsto> f x] |x. x \<in> X - {a}}"
        then show "x \<in> {[x \<mapsto> f x] |x. x \<in> X}" apply simp using Cons.prems(1) by auto
      qed
    next
      show "{[x \<mapsto> f x] |x. x \<in> X} \<subseteq> {[a \<mapsto> f a]} \<union> {[x \<mapsto> f x] |x. x \<in> X - {a}}"
      proof
        fix x
        assume "x \<in> {[x \<mapsto> f x] |x. x \<in> X}"
        then show "x \<in> {[a \<mapsto> f a]} \<union> {[x \<mapsto> f x] |x. x \<in> X - {a}}" by blast
      qed
    qed
    have a6: "card {[x \<mapsto> f x] |x. x \<in> X} = length xs + 1" using a3 a4 apply (simp add: a5)
      by (smt (verit) Cons.prems(1) card.infinite card.insert empty_set equals0I finite.emptyI 
          length_greater_0_conv list.simps(15) list.size(3) mem_Collect_eq singletonD)
    then show ?case using a1 a2 a3 a4 a5
      by (metis One_nat_def list.size(4))
  qed
  show ?thesis 
    by (smt (verit) c h1 h2 h3 length_map m map_add_seq_Merge map_eq_conv map_upd_seq_add)  
qed
*)
end