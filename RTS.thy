theory RTS
  imports ThreadState
begin

fun receiveInputSrcOld where
  "receiveInputSrcOld pki ps src dst p = (if p \<in> ps then 
  (case pki p of
    Data \<Rightarrow> Some (clear (src $ p))
  | Event \<Rightarrow> Some (tail (src $ p))
  | EventData \<Rightarrow> Some (clear (src $ p))
  )
  else None)"

fun receiveInputSrc where
  "receiveInputSrc pki ps src dst p = (if p \<in> ps then 
  (case pki p of
    Data \<Rightarrow> Some (src $ p)
  | Event \<Rightarrow> Some (tail (src $ p))
  | EventData \<Rightarrow> Some (tail (src $ p))
  )
  else None)"

fun receiveInputDstOld where
  "receiveInputDstOld pki ps src dst p = (if p \<in> ps then
  (case pki p of
    Data \<Rightarrow> Some (src $ p )
  | Event \<Rightarrow> Some (setBuffer (dst $ p) [head (src $ p)] )
  | EventData \<Rightarrow> Some (clear (dst $ p))
  )
  else None)"

fun receiveInputDst where
  "receiveInputDst pki ps src dst p = (if p \<in> ps then
  (case pki p of
    Data \<Rightarrow> Some (src $ p )
  | Event \<Rightarrow> Some (setBuffer (dst $ p) [head (src $ p)] )
  | EventData \<Rightarrow> Some (setBuffer (dst $ p) [head (src $ p)])
  )
  else None)"

inductive receiveInput for pki :: "PortId \<Rightarrow> PortKind"
                      and ps :: "PortIds"
                      and src :: "'a PortState"
                      and dst :: "'a PortState" where
  default: "receiveInput pki ps src dst 
              (receiveInputSrc pki ps src dst) 
              (receiveInputDst pki ps src dst)"

inductive sendOutput for src :: "'a PortState"
                      and dst :: "'a PortState" where
  default: "sendOutput src dst (clearAll (dom src) src) src"

end