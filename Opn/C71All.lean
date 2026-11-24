module

public import Opn.C71_0
public import Opn.C71_1
public import Opn.C71_2
public import Opn.C71_3
public import Opn.C71_4
public import Opn.C71_5


/-!
The certificate for r = 71 (`certificate table`): `cert71_checked`, from the parts.
Written by `local certificate generator`.
-/


@[expose] public section

set_option Elab.async false

open T2

theorem cert71_checked : checkCert cert71 = true :=
  checkCert_of_parts cert71 cert71_head
    (fun i hi => match i, hi with
    | 0, _ => cert71_p0
    | 1, _ => cert71_p1
    | 2, _ => cert71_p2
    | 3, _ => cert71_p3
    | 4, _ => cert71_p4
    | 5, _ => cert71_p5
    | 6, _ => cert71_p6
    | 7, _ => cert71_p7
    | 8, _ => cert71_p8
    | 9, _ => cert71_p9
    | 10, _ => cert71_p10
    | 11, _ => cert71_p11
    | 12, _ => cert71_p12
    | 13, _ => cert71_p13
    | 14, _ => cert71_p14
    | 15, _ => cert71_p15
    | 16, _ => cert71_p16
    | 17, _ => cert71_p17
    | 18, _ => cert71_p18
    | 19, _ => cert71_p19
    | 20, _ => cert71_p20
    | 21, _ => cert71_p21
    | 22, _ => cert71_p22
    | 23, _ => cert71_p23
    | 24, _ => cert71_p24
    | 25, _ => cert71_p25
    | 26, _ => cert71_p26
    | 27, _ => cert71_p27
    | 28, _ => cert71_p28
    | 29, _ => cert71_p29
    | 30, _ => cert71_p30
    | 31, _ => cert71_p31
    | 32, _ => cert71_p32
    | 33, _ => cert71_p33
    | 34, _ => cert71_p34
    | 35, _ => cert71_p35
    | 36, _ => cert71_p36
    | 37, _ => cert71_p37
    | 38, _ => cert71_p38
    | 39, _ => cert71_p39
    | 40, _ => cert71_p40
    | 41, _ => cert71_p41
    | 42, _ => cert71_p42
    | 43, _ => cert71_p43
    | 44, _ => cert71_p44
    | 45, _ => cert71_p45
    | 46, _ => cert71_p46
    | 47, _ => cert71_p47
    | 48, _ => cert71_p48
    | 49, _ => cert71_p49
    | 50, _ => cert71_p50
    | 51, _ => cert71_p51
    | 52, _ => cert71_p52
    | 53, _ => cert71_p53
    | 54, _ => cert71_p54
    | 55, _ => cert71_p55
    | 56, _ => cert71_p56
    | 57, _ => cert71_p57
    | 58, _ => cert71_p58
    | 59, _ => cert71_p59
    | 60, _ => cert71_p60
    | 61, _ => cert71_p61
    | 62, _ => cert71_p62
    | 63, _ => cert71_p63
    | 64, _ => cert71_p64
    | 65, _ => cert71_p65
    | 66, _ => cert71_p66
    | 67, _ => cert71_p67
    | 68, _ => cert71_p68
    | 69, _ => cert71_p69
    | 70, _ => cert71_p70
    | 71, _ => cert71_p71
    | 72, _ => cert71_p72
    | m + 73, h => absurd h (by rw [cert71_np]; omega))
    cert71_shape
    (fun j hj => match j, hj with
    | 0, _ => cert71_st0
    | 1, _ => cert71_st1
    | 2, _ => cert71_st2
    | 3, _ => cert71_st3
    | 4, _ => cert71_st4
    | 5, _ => cert71_st5
    | 6, _ => cert71_st6
    | 7, _ => cert71_st7
    | 8, _ => cert71_st8
    | 9, _ => cert71_st9
    | 10, _ => cert71_st10
    | m + 11, h => absurd h (by rw [cert71_nc]; omega))
    (fun j hj => match j, hj with
    | 0, _ => cert71_kt0
    | 1, _ => cert71_kt1
    | 2, _ => cert71_kt2
    | 3, _ => cert71_kt3
    | 4, _ => cert71_kt4
    | 5, _ => cert71_kt5
    | 6, _ => cert71_kt6
    | 7, _ => cert71_kt7
    | 8, _ => cert71_kt8
    | 9, _ => cert71_kt9
    | 10, _ => cert71_kt10
    | m + 11, h => absurd h (by rw [cert71_nc]; omega))
    (fun j hj => match j, hj with
    | 0, _ => cert71_n0
    | 1, _ => cert71_n1
    | 2, _ => cert71_n2
    | 3, _ => cert71_n3
    | 4, _ => cert71_n4
    | 5, _ => cert71_n5
    | 6, _ => cert71_n6
    | 7, _ => cert71_n7
    | 8, _ => cert71_n8
    | 9, _ => cert71_n9
    | 10, _ => cert71_n10
    | m + 11, h => absurd h (by rw [cert71_nc]; omega))
    cert71_owed
