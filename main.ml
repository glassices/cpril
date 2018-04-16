needs "cpril/rthm.ml";;

let refl() = mk_rthm(REFL `x:A`);;

let assume() = mk_rthm(ASSUME `x:bool`);;

let t_def() = mk_rthm(T_DEF);;

let and_def() = mk_rthm(AND_DEF);;

let lsym() = 
  reset_rcount();
  let r0 = mk_rthm(REFL `x:A`) in
  let r1 = mk_rthm(ASSUME `x:bool`) in
  let r2 = rmk_comb r0 r1 in
  let r3 = mk_rthm(REFL `x:A`) in
  let r4 = req_mp r2 r3 in
  r4,rmatch r4 ([`(p:A)=q`],`(q:A)=p`);;

let lsym'() = 
  reset_rcount();
  let r0 = mk_rthm(REFL `x:A`) in
  let r1 = mk_rthm(ASSUME `x:bool`) in
  let r2 = rmk_comb r0 r1 in
  let r3 = mk_rthm(REFL `x:A`) in
  let r4 = req_mp r2 r3 in
  r4,rmatch r4 ([`(p:A)=q`],`(\(u:B). (q:A)) = (\(u:B). p)`);;

let lsym''() = 
  reset_rcount();
  let r0 = mk_rthm(REFL `x:A`) in
  let r1 = mk_rthm(ASSUME `x:bool`) in
  let r2 = rmk_comb r0 r1 in
  let r3 = mk_rthm(REFL `x:A`) in
  let r4 = req_mp r2 r3 in
  let r5 = rabs r4 in
  r5,rmatch r5 ([`(p:A)=q`],`(\(u:B). (q:A)) = (\(u:B). p)`);;

let ltruth() =
  reset_rcount();
  let r0 = mk_rthm(REFL `x:A`) in
  let r1 = mk_rthm(T_DEF) in
  let r2 = rmk_comb r0 r1 in
  let r3 = mk_rthm(REFL `x:A`) in
  let r4 = req_mp r2 r3 in
  let r5 = rabs (mk_rthm(REFL `x:A`)) in
  let r6 = req_mp r4 r5 in
  r6,rmatch r6 ([],`T`);;

let land_intro() =
  reset_rcount();
  let r7() =
    let r4 = rmk_comb (mk_rthm(REFL `x:A`)) (mk_rthm(T_DEF)) in
    let r5 = rmk_comb r4 (mk_rthm(REFL `x:A`)) in
    let r6 = req_mp r5 (mk_rthm(REFL `x:A`)) in
    req_mp r6 (mk_rthm(REFL `x:A`)) in

  let r68() =
    let r9 = rdeduct (mk_rthm(ASSUME `x:bool`)) (r7()) 0 0 in
    let r13 = rmk_comb (mk_rthm(REFL `x:A`)) (mk_rthm(ASSUME `x:bool`)) in
    let r14 = rmk_comb r13 (mk_rthm(REFL `x:A`)) in
    let r15 = req_mp r14 (mk_rthm(REFL `x:A`)) in
    let r16 = req_mp r15 (r7()) in
    let r17 = rdeduct r16 r9 1 1 in
    req_mp r17 (mk_rthm(ASSUME `x:bool`)) in

  let r70 = rmk_comb (mk_rthm(REFL `x:A`)) (r68()) in
  let r71 = rmk_comb r70 (r68()) in
  let r74 = rmk_comb (mk_rthm(AND_DEF)) (mk_rthm(REFL `x:A`)) in
  let r76 = rmk_comb r74 (mk_rthm(REFL `x:A`)) in
  let r87 = rmk_comb (mk_rthm(REFL `x:A`)) r76 in
  let r88 = rmk_comb r87 (mk_rthm(REFL `x:A`)) in
  let r89 = req_mp r88 (mk_rthm(REFL `x:A`)) in
  let r90 = req_mp r89 r71 in
  r90,rmatch r90 ([`p:bool`;`q:bool`],`p /\ q`);;

