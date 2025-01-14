theory RTSRules
  imports ThreadState
begin


inductive receiveInputP :: "Model \<Rightarrow> CompId \<Rightarrow> PortId \<Rightarrow> 'a ThreadState \<Rightarrow> 'a ThreadState \<Rightarrow> bool" where
  dataport: "\<lbrakk>isInCIDPID m t p; \<comment> \<open>Port @{term p} must belong to thread @{term t}.\<close>
              isDataCIDPID m t p; \<comment> \<open>This rule applies when @{term p} is a data ports.\<close>
               \<comment> \<open>Consider the item @{term v} in the data port (if the thread state is well-formed, there should always be a value @{term v} in the port queue).\<close>
              portBufferPID (infi ts) p = [v];
              \<comment> \<open>Don't change (i.e., don't dequeue) the infrastructure queue @{term infi} (implicit).\<close>
              \<comment> \<open>Only set the application port state to hold the data value @{term v}.\<close>
              appi' = portReplaceBufferPID (appi ts) p [v];
              ts' = ts\<lparr> appi:= appi'\<rparr> \<rbrakk>
           \<Longrightarrow> receiveInputP m t p ts ts'"
| eventlikeportoneitem:
            "\<lbrakk>isInCIDPID m t p; \<comment> \<open>Port @{term p} must belong to thread @{term t}.\<close>
              isEventLikeCIDPID m t p;  \<comment> \<open>This rule applies when @{term p} is an event-like port.\<close>
              portHeadPID (infi ts) p = v; \<comment> \<open>Is there an item @{term v} at the head of the infrastructure queue?}\<close>
              \<comment> \<open>Dequeue the item from the infrastructure queue.}\<close>
              infi' = portDequeuePID (infi ts) p;
              \<comment> \<open>Set the application queue to hold a single value @{term v}.\<close>
              appi' = portReplaceBufferPID (appi ts) p [v];
              ts' = ts\<lparr> infi := infi', appi:= appi'\<rparr> \<rbrakk>
           \<Longrightarrow> receiveInputP m t p ts ts'"
| eventlikeportempty: "\<lbrakk>isInCIDPID m t p;
              isEventLikeCIDPID m t p;  \<comment> \<open>This rule applies when @{term p} is an event-like port.\<close>
              portBufferPID (infi ts) p = []; \<comment> \<open>Is the infrastructure queue empty?}\<close>
               \<comment> \<open>Don't change the infrastructure queue @{term infi} (implicit).\<close>
               \<comment> \<open>Set the application queue to be empty.\<close>
              appi' = portReplaceBufferPID (appi ts) p [];
              ts' = ts\<lparr> appi:= appi'\<rparr> \<rbrakk>
           \<Longrightarrow> receiveInputP m t p ts ts'"


text \<open>
Prove the frame property for the @{term receiveInput} RTS: the operation may only
change the infrastructure input @{term infi} and application input @{term appi} elements of the 
port state.  The remaining elements are unchanged.
\<close>

lemma receiveInputP_frame:
  assumes ri_assm: "receiveInputP m t p ts ts'"
  shows "(tvar ts) = (tvar ts') \<and> 
         (appo ts) = (appo ts') \<and> (info ts) = (info ts') \<and>
         (disp ts) = (disp ts')"
  using ri_assm
proof cases
  case (dataport v)
  then show ?thesis by simp
next
  case eventlikeportoneitem
  then show ?thesis by simp
next
  case eventlikeportempty
  then show ?thesis by simp
qed

lemma receiveInputP_frame2:
  assumes ri_assm: "receiveInputP m t p ts ts'"
      and other: "q \<noteq> p"
    shows "(appi ts) q = (appi ts') q \<and>
           (infi ts) q = (infi ts') q"
  using ri_assm
proof cases
  case (dataport v appi')
  then show ?thesis by (simp add: assms(2))
next
  case (eventlikeportoneitem v infi' appi')
  then show ?thesis by (simp add: other)
next
  case (eventlikeportempty appi')
  then show ?thesis by (simp add: other)
qed

lemma receiveInputP_frame3:
  assumes ri_assm: "receiveInputP m t p ts ts'"
  shows "\<exists>v w. (appi ts') = (\<lambda>a. if a = p then v else (appi ts) a) \<and>
               (infi ts') = (\<lambda>a. if a = p then w else (infi ts) a)"
  using ri_assm
proof cases
  case (dataport v appi')
  then show ?thesis by fastforce
next
  case (eventlikeportoneitem v infi' appi')
  then show ?thesis by fastforce
next
  case (eventlikeportempty appi')
  then show ?thesis by fastforce
qed


lemma receiveInputP_frame4:
  assumes ri_assm: "receiveInputP m t p ts ts'"
  shows "\<exists>v w. ts' = ts\<lparr> appi:= (\<lambda>a. if a = p then v else (appi ts) a),
                         infi:= (\<lambda>a. if a = p then w else (infi ts) a) \<rparr>"
proof -
  obtain v w where v: "(appi ts') = (\<lambda>a. if a = p then v else (appi ts) a)"
               and w: "(infi ts') = (\<lambda>a. if a = p then w else (infi ts) a)"
    using ri_assm receiveInputP_frame3 by blast
  have "(tvar ts) = (tvar ts') \<and> (appo ts) = (appo ts') \<and> (info ts) = (info ts') \<and> 
        (disp ts) = (disp ts')"
    using ri_assm receiveInputP_frame by blast
  hence "ts' = ts\<lparr> appi:= (\<lambda>a. if a = p then v else (appi ts) a),
                   infi:= (\<lambda>a. if a = p then w else (infi ts) a) \<rparr>"
    using v w by auto
  thus ?thesis by blast
qed

lemma receiveInputP_frame5:
  assumes r1: "receiveInputP m t p rs (rs\<lparr> appi:= ar, infi:= ir \<rparr>)"
      and a1: "appi rs p = appi ss p"
      and i1: "infi rs p = infi ss p"
    shows "receiveInputP m t p ss (ss\<lparr> appi:= \<lambda>a. if a = p then ar p else appi ss a,
                                       infi:= \<lambda>a. if a = p then ir p else infi ss a \<rparr>)"
  using r1
proof cases
  case (dataport v appi')
  have x1: "infi (rs\<lparr>appi := appi'\<rparr>) = infi rs" by auto
  have x2: "infi (rs\<lparr>appi := ar, infi := ir\<rparr>) = ir" by auto
  have "ir = infi rs" using x1 x2 local.dataport(5) by argo
  hence x5: "infi ss = (\<lambda>a. if a = p then ir p else infi ss a)" using i1 by force
  have x3: "appi' = ar" using local.dataport(5)
    by (metis ThreadState.ext_inject ThreadState.surjective 
              ThreadState.update_convs(1) ThreadState.update_convs(2))
  obtain appj' where x4: "appj' = portReplaceBufferPID (appi ss) p [v]" by simp
  have x6: "appj' = (\<lambda>a. if a = p then ar p else appi ss a)" 
    using a1 local.dataport(4) x3 x4 by fastforce
  have x7: "portBufferPID (infi ss) p = [v]" using i1 local.dataport(3) by auto
  have x8: "receiveInputP m t p ss (ss\<lparr>appi:= appj'\<rparr>)" 
    using local.dataport(1) local.dataport(2) receiveInputP.dataport[of m t p ss v] x4 x7
    by simp
  have "ss\<lparr>appi:= appj'\<rparr> = ss\<lparr>appi:= (\<lambda>a. if a = p then ar p else appi ss a),
                             infi:= (\<lambda>a. if a = p then ir p else infi ss a)\<rparr>"
    using x5 x6 by auto
  then show ?thesis using x8 by argo
next
  case (eventlikeportoneitem v infi' appi')
  have x1: "portHeadPID (infi ss) p = v" using i1 local.eventlikeportoneitem(3) by auto
  have x2: "infi' = ir" using local.eventlikeportoneitem(6)
    by (metis ThreadState.ext_inject ThreadState.surjective
              ThreadState.update_convs(1) ThreadState.update_convs(2))
  have x3: "appi' = ar" using local.eventlikeportoneitem(6)
    by (metis ThreadState.ext_inject ThreadState.surjective 
              ThreadState.update_convs(1) ThreadState.update_convs(2))
  obtain infj' where x4: "infj' = portDequeuePID (infi ss) p" by blast
  have x5: "infj' = (\<lambda>a. if a = p then ir p else infi ss a)"
    using i1 local.eventlikeportoneitem(4) x2 x4 by fastforce
  obtain appj' where x6: "appj' = portReplaceBufferPID (appi ss) p [v]" by blast
  have x7: "appj' = (\<lambda>a. if a = p then ar p else appi ss a)"
    using a1 local.eventlikeportoneitem(5) x3 x6 by auto
  have x8: "receiveInputP m t p ss (ss\<lparr>appi:= appj', infi:= infj'\<rparr>)"
    using x1 x4 x6 local.eventlikeportoneitem(1) local.eventlikeportoneitem(2) 
          receiveInputP.eventlikeportoneitem[of m t p ss v]
    by (metis ThreadState.surjective ThreadState.update_convs(1) ThreadState.update_convs(2))
  then show ?thesis unfolding x5 x7 by blast
next
  case (eventlikeportempty appi')
  have x1: "portBufferPID (infi ss) p = []"
    using i1 local.eventlikeportempty(3) by fastforce
  have x2: "infi (rs\<lparr>appi := ar, infi := ir\<rparr>) = ir" by auto
  have "ir = infi rs" using x1 x2 by (simp add: local.eventlikeportempty(5))
  hence x5: "infi ss = (\<lambda>a. if a = p then ir p else infi ss a)" using i1 by force
  have x3: "appi' = ar" using local.eventlikeportempty(5)
    by (metis ThreadState.select_convs(2) ThreadState.surjective 
              ThreadState.update_convs(1) ThreadState.update_convs(2))
  obtain appj' where x4: "appj' = portReplaceBufferPID (appi ss) p []" by blast
  have x6: "appj' = (\<lambda>a. if a = p then ar p else appi ss a)" 
    using a1 local.eventlikeportempty(4) x3 x4 by auto
  have x8: "receiveInputP m t p ss (ss\<lparr>appi:= appj'\<rparr>)" 
    using receiveInputP.eventlikeportempty x1 x4 
          local.eventlikeportempty(1) local.eventlikeportempty(2) by blast
  have "ss\<lparr>appi:= appj'\<rparr> = ss\<lparr>appi:= (\<lambda>a. if a = p then ar p else appi ss a),
                             infi:= (\<lambda>a. if a = p then ir p else infi ss a)\<rparr>"
    using x5 x6 by auto
  then show ?thesis using x8 by argo
qed

lemma receiveInputP_frame6:
  assumes r1: "receiveInputP m t p rs (rs\<lparr> appi:= \<lambda>a. if a = p then v else appi rs a,
                                           infi:= \<lambda>a. if a = p then w else infi rs a \<rparr>)"
      and a1: "appi rs p = appi ss p"
      and i1: "infi rs p = infi ss p"
    shows "receiveInputP m t p ss (ss\<lparr> appi:= \<lambda>a. if a = p then v else appi ss a,
                                       infi:= \<lambda>a. if a = p then w else infi ss a \<rparr>)"
proof -
  obtain ar where ar: "ar = (\<lambda>a. if a = p then v else appi rs a)" by blast
  obtain ir where ir: "ir = (\<lambda>a. if a = p then w else infi rs a)" by blast
  have h1: "ar p = v" unfolding ar by simp
  have h2: "ir p = w" unfolding ir by simp
  have h3: "receiveInputP m t p rs (rs\<lparr> appi:= ar, infi:= ir \<rparr>)"
    unfolding ar ir using r1 by blast
  hence h4: "receiveInputP m t p ss (ss\<lparr> appi:= \<lambda>a. if a = p then ar p else appi ss a,
                                       infi:= \<lambda>a. if a = p then ir p else infi ss a \<rparr>)"
    using a1 i1 receiveInputP_frame5[of m t p rs ir ar ss] by blast
  thus ?thesis unfolding h1 h2 by blast
qed

lemma receiveInputP_comm:
  assumes ne: "x \<noteq> y"
      and r1: "receiveInputP m t x ts ss"
      and r2: "receiveInputP m t y ss rs"
    shows "\<exists>us. receiveInputP m t y ts us \<and> receiveInputP m t x us rs" 
proof -
  obtain ax ix where ss: "ss = ts\<lparr> appi:= (\<lambda>a. if a = x then ax else (appi ts) a),
                                   infi:= (\<lambda>a. if a = x then ix else (infi ts) a) \<rparr>"
    using r1 receiveInputP_frame4 by blast
  obtain ay iy where rs: "rs = ss\<lparr> appi:= (\<lambda>a. if a = y then ay else (appi ss) a),
                                   infi:= (\<lambda>a. if a = y then iy else (infi ss) a) \<rparr>"
    using r2 receiveInputP_frame4 by blast
  obtain us where us: "us = ts \<lparr> appi:= (\<lambda>a. if a = y then ay else (appi ts) a),
                                 infi:= (\<lambda>a. if a = y then iy else (infi ts) a) \<rparr>" by blast
  have r0: "receiveInputP m t y ts us" unfolding us
    using ne r1 r2 receiveInputP_frame2 receiveInputP_frame6 rs by fastforce
  have h1: "appi ts x = appi us x" using ne r0 receiveInputP_frame2 by blast
  have h2: "infi ts x = infi us x" using ne r0 receiveInputP_frame2 by blast
  obtain ws where ws: "ws = us \<lparr> appi:= (\<lambda>a. if a = x then ax else (appi us) a),
                                 infi:= (\<lambda>a. if a = x then ix else (infi us) a) \<rparr>" by blast
  have h3: "receiveInputP m t x us ws" using r1 unfolding ws ss
    using h1 h2 receiveInputP_frame6[of m t x ts ix ax us] by simp
  have h4: "appi ws = appi rs" unfolding ws us rs ss using ne apply simp by fastforce
  have h5: "infi ws = infi rs" unfolding ws us rs ss using ne apply simp by fastforce
  have h6: "ws = rs" using h4 h5
    by (metis (full_types) ThreadState.equality h3 r0 r1 r2 receiveInputP_frame unit.exhaust)
  then show ?thesis using h3 r0 by blast
qed

inductive receiveInputs :: "Model \<Rightarrow> CompId \<Rightarrow> PortIds \<Rightarrow> 'a ThreadState \<Rightarrow> 'a ThreadState \<Rightarrow> bool" where
  none: "receiveInputs m t {} ts ts"
| some: "\<lbrakk>p \<in> ps; receiveInputP m t p ts ts'; receiveInputs m t (ps - {p}) ts' ts'' \<rbrakk> \<Longrightarrow> receiveInputs m t ps ts ts''"

inductive receiveInputseq :: "Model \<Rightarrow> CompId \<Rightarrow> PortId list \<Rightarrow> 'a ThreadState \<Rightarrow> 'a ThreadState \<Rightarrow> bool" where
  none: "receiveInputseq m t [] ts ts"
| some: "\<lbrakk>receiveInputP m t x ts ts'; receiveInputseq m t xs ts' ts'' \<rbrakk> \<Longrightarrow> receiveInputseq m t (x#xs) ts ts''"

lemma receiveInputP_comm_seq:
  assumes ne: "x \<noteq> y"
      and re: "receiveInputseq m t (x#y#xs) ts ts'"
    shows "receiveInputseq m t (y#x#xs) ts ts'"
proof -
  obtain ss where r1: "receiveInputP m t x ts ss"
              and r2: "receiveInputseq m t (y#xs) ss ts'"
    using re receiveInputseq.simps by force
  obtain rs where r3: "receiveInputP m t y ss rs"
              and r4: "receiveInputseq m t xs rs ts'"
    using r2 receiveInputseq.simps by force
  obtain us where u1: "receiveInputP m t y ts us" and u2: "receiveInputP m t x us rs"
    using r1 r3 receiveInputP_comm[of x y m t ts ss rs] by blast
  show ?thesis using r4 receiveInputseq.some u1 u2 by blast
qed

lemma receiveInputseq_reorder:
  assumes "set xs = set ys"
      and "length xs = n"
      and "distinct xs"
      and "distinct ys"
      and "receiveInputseq m t xs ss ts"
    shows "receiveInputseq m t ys ss ts"
  using assms
proof (induction n arbitrary: xs ys ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain a xs' where a: "xs = a#xs'" using Suc.prems(2) Suc_length_conv[of n xs] by force
  obtain b ys' where b: "ys = b#ys'" 
    using Suc.prems(1) a hd_Cons_tl[of ys] by (metis set_empty2)
  have h1: "length xs = length ys" 
    using Suc.prems(1) Suc.prems(3) Suc.prems(4) distinct_card[of xs] distinct_card[of ys]
    by argo
  hence h2: "length xs' = length ys'" by (simp add: a b)
  then show ?case
  proof (cases "xs' = []")
    case True
    have t1: "a = b" using Suc.prems(1) True a b by force
    have t2: "ys' = []" using Suc.prems(1) Suc.prems(4) True a b last_in_set by auto
    then show ?thesis using Suc.prems(5) True a b t1 by blast
  next
    case False
    hence FF: "xs' \<noteq> []" by simp
    then show ?thesis
    proof (cases "a = b")
      case True
      have f1: "a \<notin> set xs'" using Suc.prems(3) a by auto
      have f2: "a \<notin> set ys'" using Suc.prems(4) True b by force
      have "{a} \<union> set xs' = {a} \<union> set ys'" using Suc.prems(1) True a b by force
      hence f3: "set xs' = set ys'" by (simp add: f1 f2 insert_ident)
      have f4: "distinct xs'" using Suc.prems(3) a by auto
      have f5: "distinct ys'" using Suc.prems(4) b by auto
      obtain us where f6: "receiveInputP m t a ss us" and f7: "receiveInputseq m t xs' us ts"
        using Suc.prems(5) receiveInputseq.simps[of m t "a#xs'" ss ts] a apply simp by blast
      have f8: "length xs' = n" using Suc.prems(2) a by force
      have "receiveInputseq m t ys' us ts" using Suc.IH f3 f4 f5 f7 f8 by blast
      then show ?thesis using True b f6 receiveInputseq.some by blast
    next
      case False
      have f1: "a \<in> set ys'" using False Suc.prems(1) a b by auto
      have f2: "distinct (a#remove1 a ys')" using Suc.prems(4) b by force
      have f3: "set ys' = set (a#remove1 a ys')" using Suc.prems(4) b f1 by force
      obtain us where f4: "receiveInputP m t a ss us" and f5: "receiveInputseq m t xs' us ts"
        using Suc.prems(5) receiveInputseq.simps[of m t "a#xs'" ss ts] a apply simp by blast
      have f6: "set xs' = set (b#remove1 a ys')"
        using False Suc.prems(1) Suc.prems(3) Suc.prems(4) unfolding a b by fastforce
      have f7: "length xs' = n" using Suc.prems(2) a by fastforce
      have f8: "receiveInputseq m t (b#remove1 a ys') us ts"
        using Suc.IH Suc.prems(3) Suc.prems(4) f2 f5 f6 f7 unfolding a b 
        by (metis distinct.simps(2) in_set_remove1)
      have f9: "receiveInputseq m t (a#b#remove1 a ys') ss ts"
        using f4 f8 receiveInputseq.some by blast
      have g1: "receiveInputseq m t (b#a#remove1 a ys') ss ts"
        using receiveInputP_comm_seq[of a b m t "remove1 a ys'" ss ts] f9 by blast
      obtain vs where g2: "receiveInputP m t b ss vs" 
                  and g3: "receiveInputseq m t (a#remove1 a ys') vs ts"
        using receiveInputseq.simps[of m t "b#a#remove1 a ys'" ss ts] g1 by blast
      have "length ys' = n" using f7 h2 by argo
      hence g4: "length (a#remove1 a ys') = n" using Suc.prems(4) f2 f3 unfolding b
        by (metis distinct.simps(2) distinct_card)
      have "receiveInputseq m t ys' vs ts"
        using Suc.IH Suc.prems(4) f2 f3 g3 g4 unfolding b 
        by (metis distinct.simps(2))
      then show ?thesis using b g2 receiveInputseq.some by blast
    qed
  qed
qed

lemma receiveInputseqL:
  assumes d: "distinct xs"
      and s: "s = set xs"
      and r: "receiveInputs m t s ts ts'"
    shows "receiveInputseq m t xs ts ts'"
  using r s d
proof (induction arbitrary: xs rule: receiveInputs.induct)
  case (none m t ts)
  then show ?case 
    by (simp add: receiveInputseq.none)
next
  case (some p ps m t ts ts' ts'')
  have h1: "ps - {p} = set (remove1 p xs)" by (simp add: some.prems(1) some.prems(2))
  have h2: "distinct (remove1 p xs)" by (simp add: some.prems(2))
  have "receiveInputseq m t (remove1 p xs) ts' ts''" using h1 h2 some.IH by blast
  hence h3: "receiveInputseq m t (p#remove1 p xs) ts ts''" using some.hyps(2)
    using receiveInputseq.some by blast
  have h4: "set (p#remove1 p xs) = set xs" using h1 some.hyps(1) some.prems(1) by auto
  have "distinct (p#remove1 p xs)" using h1 h2 by auto
  hence "receiveInputseq m t xs ts ts''" 
    using receiveInputseq_reorder h3 h4 some.prems(2) by blast
  then show ?case by blast
qed

lemma receiveInputseqR:
  assumes d: "distinct xs"
      and r: "receiveInputseq m t xs ts ts'"
    shows "receiveInputs m t (set xs) ts ts'"
  using assms
proof (induction xs arbitrary: ts)
  case Nil
  have "{} = set []" by blast
  then show ?case 
    using receiveInputs.simps[of m t "set []" ts ts'] 
      receiveInputseq.simps[of m t "[]" ts ts'] Nil.prems(2) by fastforce
next
  case (Cons a xs)
  obtain ss where s1: "receiveInputP m t a ts ss" and s2: "receiveInputseq m t xs ss ts'"
    using receiveInputseq.cases[of m t "a#xs" ts ts'] Cons.prems(2) by blast
  have s3: "receiveInputs m t (set xs) ss ts'" using Cons.IH Cons.prems(1) s2 by force
  have s4: "set (a # xs) - {a} = set xs" using Cons.prems(1) by force
  show ?case using s1 s3 s4 receiveInputs.some[of a "set (a # xs)" m t ts ss ts'] by simp
qed

lemma receiveInputs_eq:
  assumes d: "distinct xs"
    shows "receiveInputseq m t xs ts ts' = receiveInputs m t (set xs) ts ts'"
  by (meson d receiveInputseqL receiveInputseqR)

lemma receiveInputP_wf_ThreadState: 
  assumes wf_m: "wf_Model m"
      and t_in_m: "inModelCID m t"
      and p_in_m: "inModelPID m p"
      and wf_assm: "wf_ThreadState m t ts" 
      and ri_assm: "receiveInputP m t p ts ts'"
    shows "wf_ThreadState m t ts'"
  text \<open>Intuition: The only thread state elements that may possibly change are infi and appi.
        So we establish that the other (non-changed) elements are well-formed
        from wf_assm, and then show changes to infi and appi will
        produce something that is well-formed, by consider each rule case of ReceiveInput.\<close>
proof -
  print_facts
  text \<open>First, we can conclude that all of the elements of @{term ts} are well-formed by unfolding the
        definition of wf_ThreadState.\<close>
  have wf_tvar: "wf_ThreadState_tvar m t (tvar ts)" using wf_assm by (auto simp add: wf_ThreadState_def)
  have wf_infi: "wf_ThreadState_infi m t (infi ts)" using wf_assm by (auto simp add: wf_ThreadState_def)
  have wf_appi: "wf_ThreadState_appi m t (appi ts)" using wf_assm by (auto simp add: wf_ThreadState_def)
  have wf_appo: "wf_ThreadState_appo m t (appo ts)" using wf_assm by (auto simp add: wf_ThreadState_def)
  have wf_info: "wf_ThreadState_info m t (info ts)" using wf_assm by (auto simp add: wf_ThreadState_def)
  have wf_disp: "wf_ThreadState_disp m t (disp ts)" using wf_assm by (auto simp add: wf_ThreadState_def)
  text \<open>Further, we can conclude that the port states infi and appi are well-formed port states by 
        by unfolding the definitions of well-formedness for infi and appi.\<close>
  have wf_infi_ps: "wf_PortState m (inPortsOfCID m t) (infi ts)" 
    using wf_infi unfolding wf_ThreadState_infi_def .
  have wf_appi_ps: "wf_PortState m (inPortsOfCID m t) (appi ts) " 
    using wf_appi unfolding wf_ThreadState_appi_def .
  text \<open>Next, show by rule cases that the updated infi and appi are well-formed port states and thus are
        well-formed ThreadState elements.\<close>
  have wf_infi'_appi': "wf_ThreadState_infi m t (infi ts') \<and> wf_ThreadState_appi m t (appi ts')" 
    using ri_assm
  proof cases
    case (dataport v) 
    text \<open>From the rule hypothesis, we get the structure of the updated ThreadState ts',
          in particular, the update to the appi field.\<close>
    from dataport have tspostassm: "ts' = ts\<lparr>appi := portReplaceBufferPID (appi ts) p [v]\<rparr>" by blast
    text \<open>From the rule hypothesis, we know the PortId p is an input port for Thread with id t in Model m.\<close>
    from dataport have inportassm: "isInCIDPID m t p" by blast
    text \<open>First, show that infi doesn't change for this rule, and is thus well-formed.\<close>
    have unchanged_infi: "(infi ts) = (infi ts')" using tspostassm by simp
    have wf_infi': "wf_ThreadState_infi m t (infi ts')" using wf_infi unchanged_infi by simp
    text \<open>Next, to show that appi' is well-formed, 
          first create a temporary name for the updated ThreadState field appi'.\<close>
    let ?appi' = "portReplaceBufferPID (appi ts) p [v]"
    text \<open>Show that the new buffer length is within the capacity of the queue
          (which holds because all queues have capacity ge to 1).\<close>
    from wf_m p_in_m have wf_b: "length [v] \<le> (queueSizePID m p)" 
      using wf_model_implies_port_capacity_ge_one by simp
    text \<open>Use helper lemma to show that updating the well-formed port state appi 
          using  portReplaceBufferPID preserves well-formedness.\<close>
    have wf_appi_ps_post: "wf_PortState m (inPortsOfCID m t) ?appi' "
      using wf_appi_ps inportassm wf_b portReplaceBufferPID_preserves_wf_PortState by fastforce
    text \<open>Since the updated appi is a well-formed port state, we know that it is a well-formed
          appi thread state element in ts' by definition.\<close>
    have wf_appi': "wf_ThreadState_appi m t (appi ts')" using wf_appi_ps_post tspostassm 
      unfolding  wf_ThreadState_appi_def by simp
    text \<open>Thus, we have both infi' and appi' are well-formed.\<close>
    show ?thesis using wf_infi' wf_appi' ..
  next
    case (eventlikeportempty)
    text \<open>NOTE: The proof structure for this case is identical to the one above.\<close>
    text \<open>From the rule hypothesis, we get the structure of the updated ThreadState ts',
          in particular, the update to the appi field.\<close>
    from eventlikeportempty 
      have tspostassm: "ts' = ts\<lparr>appi := portReplaceBufferPID (appi ts) p []\<rparr>" by blast
    text \<open>From the rule hypothesis, we know the PortId p is an input port for Thread with id t in Model m.\<close>
    from eventlikeportempty have inportassm: "isInCIDPID m t p" by blast
    text \<open>First, show that infi doesn't change for this rule, and is thus well-formed.\<close>
    have unchanged_infi: "(infi ts) = (infi ts')" using tspostassm by simp
    have wf_infi': "wf_ThreadState_infi m t (infi ts')" using wf_infi unchanged_infi by simp
    text \<open>Next, to show that appi' is well-formed, 
          first create a temporary name for the updated ThreadState field appi'.\<close>
    let ?appi' = "portReplaceBufferPID (appi ts) p []"
    text \<open>Show that the new buffer length is within the capacity of the queue
          (which holds because all queues have capacity ge to 1).\<close>
    from wf_m p_in_m have wf_b: "length [] \<le> (queueSizePID m p)" 
      using wf_model_implies_port_capacity_ge_one by simp
    text \<open>Use helper lemma to show that updating the well-formed port state appi 
          using  portReplaceBufferPID preserves well-formedness.\<close>
    have wf_appi_ps_post: "wf_PortState m (inPortsOfCID m t) ?appi' "
      using wf_appi_ps inportassm wf_b portReplaceBufferPID_preserves_wf_PortState by fastforce  
    text \<open>Since the updated appi is a well-formed port state, we know that it is a well-formed
          appi thread state element in ts' by definition.\<close>
    have wf_appi': "wf_ThreadState_appi m t (appi ts')" using wf_appi_ps_post tspostassm 
      unfolding  wf_ThreadState_appi_def by simp
    show ?thesis using wf_infi' wf_appi' ..
  next
    case (eventlikeportoneitem v q)
    print_cases
    print_facts
    text \<open>From the rule hypothesis, we get the structure of the updated ThreadState ts',
          in particular, the updates to the infi and appi fields.\<close>
    from eventlikeportoneitem 
      have tspostassm: "ts' = ts\<lparr> infi := portDequeuePID (infi ts) p, 
                                  appi := portReplaceBufferPID (appi ts) p [v]\<rparr>" by blast
    text \<open>From the rule hypothesis, we know the PortId p is an 
            input port for Thread with id t in Model m.\<close>
    from eventlikeportoneitem have inportassm: "isInCIDPID m t p" by blast
    text \<open>First, show that infi is thus well-formed, by relying on helper lemma showing that
          penq preserves well-formed PortStates.  First, create a temporary name for the updated 
          ThreadState field infi'\<close>
    let ?infi' = "portDequeuePID (infi ts) p"
    text \<open>Use helper lemma to show that updating the well-formed port state infi using portDequeuePID 
          preserves well-formedness. Supply preconditions that the input port state is well-formed
          and that pid argument to the operation is in the domain of the port state.\<close>
    from wf_infi_ps inportassm 
      have wf_infi_ps_post: "wf_PortState m (inPortsOfCID m t) ?infi' "
        using portDequeuePID_preserves_wf_PortState by fastforce
    text \<open>Since the updated infi is a well-formed port state, we know that it is a well-formed
          infi thread state element in ts' by definition.\<close>
    have wf_infi': "wf_ThreadState_infi m t (infi ts')" 
      using wf_infi_ps_post tspostassm 
      unfolding  wf_ThreadState_infi_def by simp
    text \<open>Next, to show that appi' is well-formed, 
          first create a temporary name for the updated ThreadState field appi'.\<close>
    let ?appi' = "portReplaceBufferPID (appi ts) p [v]"
    text \<open>Show that the new buffer length is within the capacity of the queue
          (which holds because all queues have capacity ge to 1).\<close>
    from wf_m p_in_m have wf_b: "length [v] \<le> (queueSizePID m p)" 
       using wf_model_implies_port_capacity_ge_one by simp
    text \<open>Use helper lemma to show that updating the well-formed port state appi using portReplaceBufferPID 
          preserves well-formedness. Supply preconditions that the input port state is well-formed,
          that pid argument to the operation is in the domain of the port state, and that
          the size of the new buffer is within the capacity of the port.\<close>
    from wf_appi_ps inportassm wf_b
      have wf_appi_ps_post: "wf_PortState m (inPortsOfCID m t) ?appi' "
      using portReplaceBufferPID_preserves_wf_PortState by fastforce
    text \<open>Since the updated appi is a well-formed port state, we know that it is a well-formed
          appi thread state element in ts' by definition.\<close>
    have wf_appi': "wf_ThreadState_appi m t (appi ts')" using wf_appi_ps_post tspostassm
      unfolding  wf_ThreadState_appi_def by simp
    show ?thesis using wf_infi' wf_appi' ..
  qed
  text \<open>Use helper lemma to establish the frame condition: tvar, appo, info, disp are unchanged\<close>
  have unchanged_elements: "(tvar ts) = (tvar ts') \<and> 
                            (appo ts) = (appo ts') \<and> (info ts) = (info ts') \<and>
                            (disp ts) = (disp ts')" using ri_assm by (rule receiveInputP_frame)
  text \<open>Since tvar, appo, info, disp were originally well-formed, and they have not changed, 
        we know that they are well-formed in the updated thread state ts'.\<close>
  have wf_tvar': "wf_ThreadState_tvar m t (tvar ts')" using wf_tvar unchanged_elements by auto
  have wf_appo': "wf_ThreadState_appo m t (appo ts')" using wf_appo unchanged_elements by auto
  have wf_info': "wf_ThreadState_info m t (info ts')" using wf_info unchanged_elements by auto
  have wf_disp': "wf_ThreadState_disp m t (disp ts')" using wf_disp unchanged_elements by auto
  text \<open>Since all of the new thread state elements are well-formed, then the thread state itself is 
        well-formed, by definition.\<close>
  show ?thesis unfolding wf_ThreadState_def using wf_tvar' wf_infi'_appi' wf_appo' wf_info' wf_disp' by auto
qed

lemma receiveInputseq_wf_ThreadState: 
  assumes wf_m: "wf_Model m"
      and t_in_m: "inModelCID m t"
      and p_in_m: "\<forall>p\<in>set ps. inModelPID m p"
      and wf_assm: "wf_ThreadState m t ts" 
      and ri_assm: "receiveInputseq m t ps ts ts'"
    shows "wf_ThreadState m t ts'"
  using assms
proof (induction ps arbitrary: ts)
  case Nil
  then show ?case using receiveInputseq.cases by fastforce
next
  case (Cons a ps)
  obtain rs where a1: "receiveInputP m t a ts rs" and a2: "receiveInputseq m t ps rs ts'"
    using Cons.prems(5) receiveInputseq.cases[of m t "a#ps" ts ts'] by auto
  have a3: "\<forall>a\<in>set ps. inModelPID m a" using Cons.prems(3) by auto
  then show ?case 
    using Cons.IH[of rs] Cons.prems(3) Cons.prems(4) a1 a2 wf_m t_in_m 
      receiveInputP_wf_ThreadState[of m t a] by auto
qed

lemma receiveInputs_wf_ThreadState: 
  assumes wf_m: "wf_Model m"
      and t_in_m: "inModelCID m t"
      and fin_p: "finite ps"
      and p_in_m: "\<forall>p\<in>ps. inModelPID m p"
      and wf_assm: "wf_ThreadState m t ts" 
      and ri_assm: "receiveInputs m t ps ts ts'"
    shows "wf_ThreadState m t ts'"
proof -
  obtain xs where "distinct xs" and s: "ps = set xs" using fin_p finite_distinct_list by auto
  hence "receiveInputseq m t xs ts ts'" using receiveInputs_eq ri_assm by blast
  thus ?thesis using p_in_m receiveInputseq_wf_ThreadState s t_in_m wf_assm wf_m by blast
qed

(* Needs to be reviewed. This SHA's version *)
inductive sendOutput for src :: "'a PortState"
                      and dst :: "'a PortState" where
  default: "sendOutput src dst (clearAll (dom src) src) src"

lemma sendOutput_wf_PortStates:
 assumes s: "wf_ThreadState_appo m c src"
     and d: "wf_ThreadState_info m c dst"
     and o: "sendOutput src dst src' dst'"
   shows "wf_ThreadState_appo m c src' \<and> wf_ThreadState_info m c dst'"
  using o
proof cases
  case default
  have a: "wf_ThreadState_appo m c src'" using local.default(1) s wf_clearAll_appo by blast
  have b: "wf_ThreadState_info m c dst'" by (simp add: appo_wf_info local.default(2) s)
  show ?thesis using a b by blast
qed

end