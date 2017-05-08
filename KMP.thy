(**)

theory KMP
  imports "$AFP/Refine_Imperative_HOL/IICF/IICF"
begin
  
  term "SPEC (\<lambda>x::nat. x \<in> {4,7,9})"
    
  definition "is_substring_at t s i \<equiv> take (length s) (drop i t) = s"  
    
  term "\<lambda>t s. SPEC (\<lambda>None \<Rightarrow> \<nexists>i. is_substring_at t s i | Some i \<Rightarrow> is_substring_at t s i \<and> (\<forall>j. is_substring_at t s j \<longrightarrow> i\<le>j))"
  
  
  term "RETURN (4::nat) = SPEC (\<lambda>x. x=4)" 
  
  definition "test \<equiv> do {
    x \<leftarrow> SPEC (\<lambda>x::nat. x<5);
    y \<leftarrow> SPEC (\<lambda>y. y<10);
    RETURN (x+y)
  }"  
  
  lemma "test \<le> SPEC (\<lambda>x. x<14)"
    unfolding test_def
    apply refine_vcg by auto  
  
  definition "i_test2 x\<^sub>0 \<equiv> \<lambda>(x,s). x\<ge>0 \<and> x\<^sub>0*5 = x*5+s"
  
  definition "test2 x\<^sub>0 \<equiv> do {
    (_,s) \<leftarrow> WHILEIT (i_test2 x\<^sub>0) (\<lambda>(x,s). x>0) (\<lambda>(x,s). do {
      let s = s + 5;
      let x = x - 1;
      RETURN (x,s)
    }) (x\<^sub>0::int,0::int);
    RETURN s
  }"  
  
  term "measure (nat o fst)"
    
  lemma "x\<ge>0 \<Longrightarrow> test2 x \<le> SPEC (\<lambda>r. r=x*5)"
    unfolding test2_def i_test2_def
    apply (refine_vcg WHILEIT_rule[where R="measure (nat o fst)"])  
    apply auto  
    done
      

section\<open>Naive algorithm\<close>
    
subsection\<open>Invariants\<close>
  definition "I_out_na t s \<equiv> \<lambda>(i,j(*_?*),found).
    \<not>found \<and> j = 0 \<and> (\<forall>i' < i. \<not>is_substring_at t s i')
    \<or> found \<and> is_substring_at t s i"  
  definition "I_in_na t s iout (*KMP should need jout, too*) \<equiv> \<lambda>(j,found).
    \<not>found \<and> j < length s \<and> (\<forall>j' < j. t!(iout+j') = s!(j'))
    \<or> found \<and> j = length s \<and> is_substring_at t s iout"

subsection\<open>Algorithm\<close>
  definition "na t s \<equiv> do {
    let i=0;
    let j=0;
    (_,_,found) \<leftarrow> WHILEI (I_out_na t s) (\<lambda>(i,j,found). i\<le>length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
      (j,found) \<leftarrow> WHILEI (I_in_na t s i) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
        let j=j+1;
        if j=length s then RETURN (j,True) else RETURN (j,False)
      }) (j,found);
      if \<not>found then do {
        let i = i + 1;
        let j = 0;
        RETURN (i,j,False)
      } else RETURN (i,j,True)
    }) (i,j,False);

    RETURN found
  }"

lemma all_positions_step:
  "\<lbrakk>\<forall>j'<aba. t ! (ab + j') = s ! j'; t ! (ab + aba) = s ! aba\<rbrakk>
       \<Longrightarrow> \<forall>j'\<le>aba. t ! (ab + j') = s ! j'"
  using le_neq_implies_less by blast

lemma all_positions_substring:
"\<lbrakk>(*Todo: Copy from subgoal*)True\<rbrakk>
       \<Longrightarrow> is_substring_at t s ab"
  unfolding is_substring_at_def
  oops
      
lemma "\<lbrakk>s \<noteq> []; t \<noteq> []; length s \<le> length t\<rbrakk>
  \<Longrightarrow> na t s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. is_substring_at t s i))"
    unfolding na_def I_out_na_def I_in_na_def
    (*are these safe?*)apply refine_vcg apply vc_solve
    using is_substring_at_def
    (*...*)
    defer
    using less_antisym apply blast
      apply (smt add_le_imp_le_left is_substring_at_def leD le_trans less_Suc_eq nat_le_linear nth_drop nth_take order_trans ordered_cancel_comm_monoid_diff_class.le_diff_conv2)
    using is_substring_at_def
    oops

(*ToDo: WHILET statt WHILE*)
text\<open>Zusätzliche Voraussetzungen nötig! Auch Seidl sagen?\<close>
      
section\<open>Knuth–Morris–Pratt algorithm\<close>
subsection\<open>Auxiliary definitions\<close>
  definition border :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where "border s j \<equiv> undefined"
  
  (*Todo: Properties*)
  thm longest_common_prefix

subsection\<open>Invariants\<close>
  definition "I_outer \<equiv> \<lambda>(i,j,found). undefined"  
  definition "I_inner iout jout \<equiv> \<lambda>(j,found). undefined"  

subsection\<open>Algorithm\<close>
  definition "kmp t s \<equiv> do {
    let i=0; let j=0;

    (_,_,found) \<leftarrow> WHILEI I_outer (\<lambda>(i,j,found). i\<le>length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
      (j,found) \<leftarrow> WHILEI (I_inner i j) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
        let j=j+1;
        if j=length s then RETURN (j,True) else RETURN (j,False)
      }) (j,found);
      if \<not>found then do {
        let i = i + (j + 1 - border s j);
        let j = max 0 (border s j - 1); (*max not necessary*)
        RETURN (i,j,False)
      } else RETURN (i,j,True)
    }) (i,j,False);

    RETURN found
  }"
      
    
    
  lemma "kmp t s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. is_substring_at t s i))"
    unfolding kmp_def
    apply refine_vcg  
    apply vc_solve  
  
  
  
