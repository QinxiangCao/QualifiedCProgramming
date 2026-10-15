import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.Prime
import Mathlib.Data.List.Range

set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
open AUXLib.Prime

def SieveCount.trial_primes : List Int := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173]
open SieveCount

def SieveCount.bounded_primes : List Int :=
  ((List.range 31624).map (fun (n:Nat)=>(n:Int))).filter
    (fun p => trial_primes.all (fun q=>(p==q) || !(Z.modulo p q==0)))

theorem bounded_primes_complete__sieve_construction (p : Int) (hb : 0≤p ∧ p≤31623) (hp : prime p) :
    p∈bounded_primes := by
  apply List.mem_filter.mpr
  refine ⟨?_,?_⟩
  · exact List.mem_map.mpr ⟨p.toNat,List.mem_range.mpr (by omega),by omega⟩
  · apply List.all_eq_true.mpr
    intro q hq
    have hqb : 2≤q ∧ q≤173 := by
      simp only [trial_primes,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq|hq <;> omega
    by_cases he : p=q
    · simp [he]
    · have hm : Z.modulo p q≠0 := by
        intro hm
        have hd : q∣p := Int.dvd_of_emod_eq_zero (by simpa only [Z.modulo,Int.fmod_eq_emod_of_nonneg p (by omega : 0≤q)] using hm)
        have hc := prime_divisors p hp q ((Z.divide_iff_dvd _ _).mpr hd)
        have := prime_ge_2 p hp
        omega
      simp [he,hm]

-- Split the finite sieve calculation into small kernel-checked blocks.
-- This avoids native_decide and its external evaluation axiom.
private def trial_count (start count : Nat) : Nat :=
  (((List.range' start count).map (fun (n:Nat)=>(n:Int))).filter
    (fun p=>trial_primes.all (fun q=>(p==q) || !(Z.modulo p q==0)))).length
private theorem trial_count_add (start m n : Nat) :
    trial_count start (m+n)=trial_count start m+trial_count (start+m) n := by
  unfold trial_count
  rw [←List.range'_append_1 (s:=start) (m:=m) (n:=n),List.map_append,List.filter_append,List.length_append]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_0 : trial_count 0 256=55 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_256 : trial_count 256 256=43 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_512 : trial_count 512 256=38 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_768 : trial_count 768 256=37 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_1024 : trial_count 1024 256=35 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_1280 : trial_count 1280 256=35 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_1536 : trial_count 1536 256=36 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_1792 : trial_count 1792 256=31 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_2048 : trial_count 2048 256=33 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_2304 : trial_count 2304 256=33 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_2560 : trial_count 2560 256=34 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_2816 : trial_count 2816 256=30 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_3072 : trial_count 3072 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_3328 : trial_count 3328 256=34 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_3584 : trial_count 3584 256=30 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_3840 : trial_count 3840 256=32 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_4096 : trial_count 4096 256=30 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_4352 : trial_count 4352 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_4608 : trial_count 4608 256=28 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_4864 : trial_count 4864 256=34 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_5120 : trial_count 5120 256=23 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_5376 : trial_count 5376 256=31 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_5632 : trial_count 5632 256=36 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_5888 : trial_count 5888 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_6144 : trial_count 6144 256=33 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_6400 : trial_count 6400 256=23 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_6656 : trial_count 6656 256=32 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_6912 : trial_count 6912 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_7168 : trial_count 7168 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_7424 : trial_count 7424 256=32 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_7680 : trial_count 7680 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_7936 : trial_count 7936 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_8192 : trial_count 8192 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_8448 : trial_count 8448 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_8704 : trial_count 8704 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_8960 : trial_count 8960 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_9216 : trial_count 9216 256=31 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_9472 : trial_count 9472 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_9728 : trial_count 9728 256=30 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_9984 : trial_count 9984 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_10240 : trial_count 10240 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_10496 : trial_count 10496 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_10752 : trial_count 10752 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_11008 : trial_count 11008 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_11264 : trial_count 11264 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_11520 : trial_count 11520 256=20 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_11776 : trial_count 11776 256=31 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_12032 : trial_count 12032 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_12288 : trial_count 12288 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_12544 : trial_count 12544 256=28 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_12800 : trial_count 12800 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_13056 : trial_count 13056 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_13312 : trial_count 13312 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_13568 : trial_count 13568 256=28 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_13824 : trial_count 13824 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_14080 : trial_count 14080 256=22 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_14336 : trial_count 14336 256=28 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_14592 : trial_count 14592 256=30 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_14848 : trial_count 14848 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_15104 : trial_count 15104 256=30 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_15360 : trial_count 15360 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_15616 : trial_count 15616 256=28 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_15872 : trial_count 15872 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_16128 : trial_count 16128 256=23 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_16384 : trial_count 16384 256=24 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_16640 : trial_count 16640 256=24 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_16896 : trial_count 16896 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_17152 : trial_count 17152 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_17408 : trial_count 17408 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_17664 : trial_count 17664 256=24 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_17920 : trial_count 17920 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_18176 : trial_count 18176 256=28 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_18432 : trial_count 18432 256=23 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_18688 : trial_count 18688 256=21 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_18944 : trial_count 18944 256=22 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_19200 : trial_count 19200 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_19456 : trial_count 19456 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_19712 : trial_count 19712 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_19968 : trial_count 19968 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_20224 : trial_count 20224 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_20480 : trial_count 20480 256=22 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_20736 : trial_count 20736 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_20992 : trial_count 20992 256=28 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_21248 : trial_count 21248 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_21504 : trial_count 21504 256=28 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_21760 : trial_count 21760 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_22016 : trial_count 22016 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_22272 : trial_count 22272 256=24 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_22528 : trial_count 22528 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_22784 : trial_count 22784 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_23040 : trial_count 23040 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_23296 : trial_count 23296 256=21 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_23552 : trial_count 23552 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_23808 : trial_count 23808 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_24064 : trial_count 24064 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_24320 : trial_count 24320 256=24 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_24576 : trial_count 24576 256=20 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_24832 : trial_count 24832 256=24 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_25088 : trial_count 25088 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_25344 : trial_count 25344 256=23 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_25600 : trial_count 25600 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_25856 : trial_count 25856 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_26112 : trial_count 26112 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_26368 : trial_count 26368 256=22 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_26624 : trial_count 26624 256=30 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_26880 : trial_count 26880 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_27136 : trial_count 27136 256=18 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_27392 : trial_count 27392 256=23 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_27648 : trial_count 27648 256=29 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_27904 : trial_count 27904 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_28160 : trial_count 28160 256=22 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_28416 : trial_count 28416 256=32 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_28672 : trial_count 28672 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_28928 : trial_count 28928 256=23 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_29184 : trial_count 29184 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_29440 : trial_count 29440 256=22 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_29696 : trial_count 29696 256=21 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_29952 : trial_count 29952 256=25 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_30208 : trial_count 30208 256=21 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_30464 : trial_count 30464 256=26 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_30720 : trial_count 30720 256=24 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_30976 : trial_count 30976 256=27 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_31232 : trial_count 31232 256=23 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem trial_block_31488 : trial_count 31488 136=13 := by decide +kernel

private theorem trial_tail_31488 : trial_count 31488 136=13 := by
  exact trial_block_31488

private theorem trial_tail_31232 : trial_count 31232 392=36 := by
  rw [show 392=256+136 from rfl,trial_count_add,trial_block_31232,show 31232+256=31488 from rfl,trial_tail_31488]

private theorem trial_tail_30976 : trial_count 30976 648=63 := by
  rw [show 648=256+392 from rfl,trial_count_add,trial_block_30976,show 30976+256=31232 from rfl,trial_tail_31232]

private theorem trial_tail_30720 : trial_count 30720 904=87 := by
  rw [show 904=256+648 from rfl,trial_count_add,trial_block_30720,show 30720+256=30976 from rfl,trial_tail_30976]

private theorem trial_tail_30464 : trial_count 30464 1160=113 := by
  rw [show 1160=256+904 from rfl,trial_count_add,trial_block_30464,show 30464+256=30720 from rfl,trial_tail_30720]

private theorem trial_tail_30208 : trial_count 30208 1416=134 := by
  rw [show 1416=256+1160 from rfl,trial_count_add,trial_block_30208,show 30208+256=30464 from rfl,trial_tail_30464]

private theorem trial_tail_29952 : trial_count 29952 1672=159 := by
  rw [show 1672=256+1416 from rfl,trial_count_add,trial_block_29952,show 29952+256=30208 from rfl,trial_tail_30208]

private theorem trial_tail_29696 : trial_count 29696 1928=180 := by
  rw [show 1928=256+1672 from rfl,trial_count_add,trial_block_29696,show 29696+256=29952 from rfl,trial_tail_29952]

private theorem trial_tail_29440 : trial_count 29440 2184=202 := by
  rw [show 2184=256+1928 from rfl,trial_count_add,trial_block_29440,show 29440+256=29696 from rfl,trial_tail_29696]

private theorem trial_tail_29184 : trial_count 29184 2440=229 := by
  rw [show 2440=256+2184 from rfl,trial_count_add,trial_block_29184,show 29184+256=29440 from rfl,trial_tail_29440]

private theorem trial_tail_28928 : trial_count 28928 2696=252 := by
  rw [show 2696=256+2440 from rfl,trial_count_add,trial_block_28928,show 28928+256=29184 from rfl,trial_tail_29184]

private theorem trial_tail_28672 : trial_count 28672 2952=277 := by
  rw [show 2952=256+2696 from rfl,trial_count_add,trial_block_28672,show 28672+256=28928 from rfl,trial_tail_28928]

private theorem trial_tail_28416 : trial_count 28416 3208=309 := by
  rw [show 3208=256+2952 from rfl,trial_count_add,trial_block_28416,show 28416+256=28672 from rfl,trial_tail_28672]

private theorem trial_tail_28160 : trial_count 28160 3464=331 := by
  rw [show 3464=256+3208 from rfl,trial_count_add,trial_block_28160,show 28160+256=28416 from rfl,trial_tail_28416]

private theorem trial_tail_27904 : trial_count 27904 3720=356 := by
  rw [show 3720=256+3464 from rfl,trial_count_add,trial_block_27904,show 27904+256=28160 from rfl,trial_tail_28160]

private theorem trial_tail_27648 : trial_count 27648 3976=385 := by
  rw [show 3976=256+3720 from rfl,trial_count_add,trial_block_27648,show 27648+256=27904 from rfl,trial_tail_27904]

private theorem trial_tail_27392 : trial_count 27392 4232=408 := by
  rw [show 4232=256+3976 from rfl,trial_count_add,trial_block_27392,show 27392+256=27648 from rfl,trial_tail_27648]

private theorem trial_tail_27136 : trial_count 27136 4488=426 := by
  rw [show 4488=256+4232 from rfl,trial_count_add,trial_block_27136,show 27136+256=27392 from rfl,trial_tail_27392]

private theorem trial_tail_26880 : trial_count 26880 4744=453 := by
  rw [show 4744=256+4488 from rfl,trial_count_add,trial_block_26880,show 26880+256=27136 from rfl,trial_tail_27136]

private theorem trial_tail_26624 : trial_count 26624 5000=483 := by
  rw [show 5000=256+4744 from rfl,trial_count_add,trial_block_26624,show 26624+256=26880 from rfl,trial_tail_26880]

private theorem trial_tail_26368 : trial_count 26368 5256=505 := by
  rw [show 5256=256+5000 from rfl,trial_count_add,trial_block_26368,show 26368+256=26624 from rfl,trial_tail_26624]

private theorem trial_tail_26112 : trial_count 26112 5512=531 := by
  rw [show 5512=256+5256 from rfl,trial_count_add,trial_block_26112,show 26112+256=26368 from rfl,trial_tail_26368]

private theorem trial_tail_25856 : trial_count 25856 5768=556 := by
  rw [show 5768=256+5512 from rfl,trial_count_add,trial_block_25856,show 25856+256=26112 from rfl,trial_tail_26112]

private theorem trial_tail_25600 : trial_count 25600 6024=583 := by
  rw [show 6024=256+5768 from rfl,trial_count_add,trial_block_25600,show 25600+256=25856 from rfl,trial_tail_25856]

private theorem trial_tail_25344 : trial_count 25344 6280=606 := by
  rw [show 6280=256+6024 from rfl,trial_count_add,trial_block_25344,show 25344+256=25600 from rfl,trial_tail_25600]

private theorem trial_tail_25088 : trial_count 25088 6536=632 := by
  rw [show 6536=256+6280 from rfl,trial_count_add,trial_block_25088,show 25088+256=25344 from rfl,trial_tail_25344]

private theorem trial_tail_24832 : trial_count 24832 6792=656 := by
  rw [show 6792=256+6536 from rfl,trial_count_add,trial_block_24832,show 24832+256=25088 from rfl,trial_tail_25088]

private theorem trial_tail_24576 : trial_count 24576 7048=676 := by
  rw [show 7048=256+6792 from rfl,trial_count_add,trial_block_24576,show 24576+256=24832 from rfl,trial_tail_24832]

private theorem trial_tail_24320 : trial_count 24320 7304=700 := by
  rw [show 7304=256+7048 from rfl,trial_count_add,trial_block_24320,show 24320+256=24576 from rfl,trial_tail_24576]

private theorem trial_tail_24064 : trial_count 24064 7560=725 := by
  rw [show 7560=256+7304 from rfl,trial_count_add,trial_block_24064,show 24064+256=24320 from rfl,trial_tail_24320]

private theorem trial_tail_23808 : trial_count 23808 7816=754 := by
  rw [show 7816=256+7560 from rfl,trial_count_add,trial_block_23808,show 23808+256=24064 from rfl,trial_tail_24064]

private theorem trial_tail_23552 : trial_count 23552 8072=783 := by
  rw [show 8072=256+7816 from rfl,trial_count_add,trial_block_23552,show 23552+256=23808 from rfl,trial_tail_23808]

private theorem trial_tail_23296 : trial_count 23296 8328=804 := by
  rw [show 8328=256+8072 from rfl,trial_count_add,trial_block_23296,show 23296+256=23552 from rfl,trial_tail_23552]

private theorem trial_tail_23040 : trial_count 23040 8584=830 := by
  rw [show 8584=256+8328 from rfl,trial_count_add,trial_block_23040,show 23040+256=23296 from rfl,trial_tail_23296]

private theorem trial_tail_22784 : trial_count 22784 8840=855 := by
  rw [show 8840=256+8584 from rfl,trial_count_add,trial_block_22784,show 22784+256=23040 from rfl,trial_tail_23040]

private theorem trial_tail_22528 : trial_count 22528 9096=884 := by
  rw [show 9096=256+8840 from rfl,trial_count_add,trial_block_22528,show 22528+256=22784 from rfl,trial_tail_22784]

private theorem trial_tail_22272 : trial_count 22272 9352=908 := by
  rw [show 9352=256+9096 from rfl,trial_count_add,trial_block_22272,show 22272+256=22528 from rfl,trial_tail_22528]

private theorem trial_tail_22016 : trial_count 22016 9608=935 := by
  rw [show 9608=256+9352 from rfl,trial_count_add,trial_block_22016,show 22016+256=22272 from rfl,trial_tail_22272]

private theorem trial_tail_21760 : trial_count 21760 9864=960 := by
  rw [show 9864=256+9608 from rfl,trial_count_add,trial_block_21760,show 21760+256=22016 from rfl,trial_tail_22016]

private theorem trial_tail_21504 : trial_count 21504 10120=988 := by
  rw [show 10120=256+9864 from rfl,trial_count_add,trial_block_21504,show 21504+256=21760 from rfl,trial_tail_21760]

private theorem trial_tail_21248 : trial_count 21248 10376=1013 := by
  rw [show 10376=256+10120 from rfl,trial_count_add,trial_block_21248,show 21248+256=21504 from rfl,trial_tail_21504]

private theorem trial_tail_20992 : trial_count 20992 10632=1041 := by
  rw [show 10632=256+10376 from rfl,trial_count_add,trial_block_20992,show 20992+256=21248 from rfl,trial_tail_21248]

private theorem trial_tail_20736 : trial_count 20736 10888=1067 := by
  rw [show 10888=256+10632 from rfl,trial_count_add,trial_block_20736,show 20736+256=20992 from rfl,trial_tail_20992]

private theorem trial_tail_20480 : trial_count 20480 11144=1089 := by
  rw [show 11144=256+10888 from rfl,trial_count_add,trial_block_20480,show 20480+256=20736 from rfl,trial_tail_20736]

private theorem trial_tail_20224 : trial_count 20224 11400=1115 := by
  rw [show 11400=256+11144 from rfl,trial_count_add,trial_block_20224,show 20224+256=20480 from rfl,trial_tail_20480]

private theorem trial_tail_19968 : trial_count 19968 11656=1144 := by
  rw [show 11656=256+11400 from rfl,trial_count_add,trial_block_19968,show 19968+256=20224 from rfl,trial_tail_20224]

private theorem trial_tail_19712 : trial_count 19712 11912=1170 := by
  rw [show 11912=256+11656 from rfl,trial_count_add,trial_block_19712,show 19712+256=19968 from rfl,trial_tail_19968]

private theorem trial_tail_19456 : trial_count 19456 12168=1196 := by
  rw [show 12168=256+11912 from rfl,trial_count_add,trial_block_19456,show 19456+256=19712 from rfl,trial_tail_19712]

private theorem trial_tail_19200 : trial_count 19200 12424=1225 := by
  rw [show 12424=256+12168 from rfl,trial_count_add,trial_block_19200,show 19200+256=19456 from rfl,trial_tail_19456]

private theorem trial_tail_18944 : trial_count 18944 12680=1247 := by
  rw [show 12680=256+12424 from rfl,trial_count_add,trial_block_18944,show 18944+256=19200 from rfl,trial_tail_19200]

private theorem trial_tail_18688 : trial_count 18688 12936=1268 := by
  rw [show 12936=256+12680 from rfl,trial_count_add,trial_block_18688,show 18688+256=18944 from rfl,trial_tail_18944]

private theorem trial_tail_18432 : trial_count 18432 13192=1291 := by
  rw [show 13192=256+12936 from rfl,trial_count_add,trial_block_18432,show 18432+256=18688 from rfl,trial_tail_18688]

private theorem trial_tail_18176 : trial_count 18176 13448=1319 := by
  rw [show 13448=256+13192 from rfl,trial_count_add,trial_block_18176,show 18176+256=18432 from rfl,trial_tail_18432]

private theorem trial_tail_17920 : trial_count 17920 13704=1348 := by
  rw [show 13704=256+13448 from rfl,trial_count_add,trial_block_17920,show 17920+256=18176 from rfl,trial_tail_18176]

private theorem trial_tail_17664 : trial_count 17664 13960=1372 := by
  rw [show 13960=256+13704 from rfl,trial_count_add,trial_block_17664,show 17664+256=17920 from rfl,trial_tail_17920]

private theorem trial_tail_17408 : trial_count 17408 14216=1399 := by
  rw [show 14216=256+13960 from rfl,trial_count_add,trial_block_17408,show 17408+256=17664 from rfl,trial_tail_17664]

private theorem trial_tail_17152 : trial_count 17152 14472=1426 := by
  rw [show 14472=256+14216 from rfl,trial_count_add,trial_block_17152,show 17152+256=17408 from rfl,trial_tail_17408]

private theorem trial_tail_16896 : trial_count 16896 14728=1453 := by
  rw [show 14728=256+14472 from rfl,trial_count_add,trial_block_16896,show 16896+256=17152 from rfl,trial_tail_17152]

private theorem trial_tail_16640 : trial_count 16640 14984=1477 := by
  rw [show 14984=256+14728 from rfl,trial_count_add,trial_block_16640,show 16640+256=16896 from rfl,trial_tail_16896]

private theorem trial_tail_16384 : trial_count 16384 15240=1501 := by
  rw [show 15240=256+14984 from rfl,trial_count_add,trial_block_16384,show 16384+256=16640 from rfl,trial_tail_16640]

private theorem trial_tail_16128 : trial_count 16128 15496=1524 := by
  rw [show 15496=256+15240 from rfl,trial_count_add,trial_block_16128,show 16128+256=16384 from rfl,trial_tail_16384]

private theorem trial_tail_15872 : trial_count 15872 15752=1553 := by
  rw [show 15752=256+15496 from rfl,trial_count_add,trial_block_15872,show 15872+256=16128 from rfl,trial_tail_16128]

private theorem trial_tail_15616 : trial_count 15616 16008=1581 := by
  rw [show 16008=256+15752 from rfl,trial_count_add,trial_block_15616,show 15616+256=15872 from rfl,trial_tail_15872]

private theorem trial_tail_15360 : trial_count 15360 16264=1607 := by
  rw [show 16264=256+16008 from rfl,trial_count_add,trial_block_15360,show 15360+256=15616 from rfl,trial_tail_15616]

private theorem trial_tail_15104 : trial_count 15104 16520=1637 := by
  rw [show 16520=256+16264 from rfl,trial_count_add,trial_block_15104,show 15104+256=15360 from rfl,trial_tail_15360]

private theorem trial_tail_14848 : trial_count 14848 16776=1662 := by
  rw [show 16776=256+16520 from rfl,trial_count_add,trial_block_14848,show 14848+256=15104 from rfl,trial_tail_15104]

private theorem trial_tail_14592 : trial_count 14592 17032=1692 := by
  rw [show 17032=256+16776 from rfl,trial_count_add,trial_block_14592,show 14592+256=14848 from rfl,trial_tail_14848]

private theorem trial_tail_14336 : trial_count 14336 17288=1720 := by
  rw [show 17288=256+17032 from rfl,trial_count_add,trial_block_14336,show 14336+256=14592 from rfl,trial_tail_14592]

private theorem trial_tail_14080 : trial_count 14080 17544=1742 := by
  rw [show 17544=256+17288 from rfl,trial_count_add,trial_block_14080,show 14080+256=14336 from rfl,trial_tail_14336]

private theorem trial_tail_13824 : trial_count 13824 17800=1768 := by
  rw [show 17800=256+17544 from rfl,trial_count_add,trial_block_13824,show 13824+256=14080 from rfl,trial_tail_14080]

private theorem trial_tail_13568 : trial_count 13568 18056=1796 := by
  rw [show 18056=256+17800 from rfl,trial_count_add,trial_block_13568,show 13568+256=13824 from rfl,trial_tail_13824]

private theorem trial_tail_13312 : trial_count 13312 18312=1821 := by
  rw [show 18312=256+18056 from rfl,trial_count_add,trial_block_13312,show 13312+256=13568 from rfl,trial_tail_13568]

private theorem trial_tail_13056 : trial_count 13056 18568=1846 := by
  rw [show 18568=256+18312 from rfl,trial_count_add,trial_block_13056,show 13056+256=13312 from rfl,trial_tail_13312]

private theorem trial_tail_12800 : trial_count 12800 18824=1875 := by
  rw [show 18824=256+18568 from rfl,trial_count_add,trial_block_12800,show 12800+256=13056 from rfl,trial_tail_13056]

private theorem trial_tail_12544 : trial_count 12544 19080=1903 := by
  rw [show 19080=256+18824 from rfl,trial_count_add,trial_block_12544,show 12544+256=12800 from rfl,trial_tail_12800]

private theorem trial_tail_12288 : trial_count 12288 19336=1932 := by
  rw [show 19336=256+19080 from rfl,trial_count_add,trial_block_12288,show 12288+256=12544 from rfl,trial_tail_12544]

private theorem trial_tail_12032 : trial_count 12032 19592=1961 := by
  rw [show 19592=256+19336 from rfl,trial_count_add,trial_block_12032,show 12032+256=12288 from rfl,trial_tail_12288]

private theorem trial_tail_11776 : trial_count 11776 19848=1992 := by
  rw [show 19848=256+19592 from rfl,trial_count_add,trial_block_11776,show 11776+256=12032 from rfl,trial_tail_12032]

private theorem trial_tail_11520 : trial_count 11520 20104=2012 := by
  rw [show 20104=256+19848 from rfl,trial_count_add,trial_block_11520,show 11520+256=11776 from rfl,trial_tail_11776]

private theorem trial_tail_11264 : trial_count 11264 20360=2039 := by
  rw [show 20360=256+20104 from rfl,trial_count_add,trial_block_11264,show 11264+256=11520 from rfl,trial_tail_11520]

private theorem trial_tail_11008 : trial_count 11008 20616=2065 := by
  rw [show 20616=256+20360 from rfl,trial_count_add,trial_block_11008,show 11008+256=11264 from rfl,trial_tail_11264]

private theorem trial_tail_10752 : trial_count 10752 20872=2091 := by
  rw [show 20872=256+20616 from rfl,trial_count_add,trial_block_10752,show 10752+256=11008 from rfl,trial_tail_11008]

private theorem trial_tail_10496 : trial_count 10496 21128=2118 := by
  rw [show 21128=256+20872 from rfl,trial_count_add,trial_block_10496,show 10496+256=10752 from rfl,trial_tail_10752]

private theorem trial_tail_10240 : trial_count 10240 21384=2147 := by
  rw [show 21384=256+21128 from rfl,trial_count_add,trial_block_10240,show 10240+256=10496 from rfl,trial_tail_10496]

private theorem trial_tail_9984 : trial_count 9984 21640=2172 := by
  rw [show 21640=256+21384 from rfl,trial_count_add,trial_block_9984,show 9984+256=10240 from rfl,trial_tail_10240]

private theorem trial_tail_9728 : trial_count 9728 21896=2202 := by
  rw [show 21896=256+21640 from rfl,trial_count_add,trial_block_9728,show 9728+256=9984 from rfl,trial_tail_9984]

private theorem trial_tail_9472 : trial_count 9472 22152=2228 := by
  rw [show 22152=256+21896 from rfl,trial_count_add,trial_block_9472,show 9472+256=9728 from rfl,trial_tail_9728]

private theorem trial_tail_9216 : trial_count 9216 22408=2259 := by
  rw [show 22408=256+22152 from rfl,trial_count_add,trial_block_9216,show 9216+256=9472 from rfl,trial_tail_9472]

private theorem trial_tail_8960 : trial_count 8960 22664=2288 := by
  rw [show 22664=256+22408 from rfl,trial_count_add,trial_block_8960,show 8960+256=9216 from rfl,trial_tail_9216]

private theorem trial_tail_8704 : trial_count 8704 22920=2317 := by
  rw [show 22920=256+22664 from rfl,trial_count_add,trial_block_8704,show 8704+256=8960 from rfl,trial_tail_8960]

private theorem trial_tail_8448 : trial_count 8448 23176=2344 := by
  rw [show 23176=256+22920 from rfl,trial_count_add,trial_block_8448,show 8448+256=8704 from rfl,trial_tail_8704]

private theorem trial_tail_8192 : trial_count 8192 23432=2373 := by
  rw [show 23432=256+23176 from rfl,trial_count_add,trial_block_8192,show 8192+256=8448 from rfl,trial_tail_8448]

private theorem trial_tail_7936 : trial_count 7936 23688=2399 := by
  rw [show 23688=256+23432 from rfl,trial_count_add,trial_block_7936,show 7936+256=8192 from rfl,trial_tail_8192]

private theorem trial_tail_7680 : trial_count 7680 23944=2428 := by
  rw [show 23944=256+23688 from rfl,trial_count_add,trial_block_7680,show 7680+256=7936 from rfl,trial_tail_7936]

private theorem trial_tail_7424 : trial_count 7424 24200=2460 := by
  rw [show 24200=256+23944 from rfl,trial_count_add,trial_block_7424,show 7424+256=7680 from rfl,trial_tail_7680]

private theorem trial_tail_7168 : trial_count 7168 24456=2485 := by
  rw [show 24456=256+24200 from rfl,trial_count_add,trial_block_7168,show 7168+256=7424 from rfl,trial_tail_7424]

private theorem trial_tail_6912 : trial_count 6912 24712=2512 := by
  rw [show 24712=256+24456 from rfl,trial_count_add,trial_block_6912,show 6912+256=7168 from rfl,trial_tail_7168]

private theorem trial_tail_6656 : trial_count 6656 24968=2544 := by
  rw [show 24968=256+24712 from rfl,trial_count_add,trial_block_6656,show 6656+256=6912 from rfl,trial_tail_6912]

private theorem trial_tail_6400 : trial_count 6400 25224=2567 := by
  rw [show 25224=256+24968 from rfl,trial_count_add,trial_block_6400,show 6400+256=6656 from rfl,trial_tail_6656]

private theorem trial_tail_6144 : trial_count 6144 25480=2600 := by
  rw [show 25480=256+25224 from rfl,trial_count_add,trial_block_6144,show 6144+256=6400 from rfl,trial_tail_6400]

private theorem trial_tail_5888 : trial_count 5888 25736=2626 := by
  rw [show 25736=256+25480 from rfl,trial_count_add,trial_block_5888,show 5888+256=6144 from rfl,trial_tail_6144]

private theorem trial_tail_5632 : trial_count 5632 25992=2662 := by
  rw [show 25992=256+25736 from rfl,trial_count_add,trial_block_5632,show 5632+256=5888 from rfl,trial_tail_5888]

private theorem trial_tail_5376 : trial_count 5376 26248=2693 := by
  rw [show 26248=256+25992 from rfl,trial_count_add,trial_block_5376,show 5376+256=5632 from rfl,trial_tail_5632]

private theorem trial_tail_5120 : trial_count 5120 26504=2716 := by
  rw [show 26504=256+26248 from rfl,trial_count_add,trial_block_5120,show 5120+256=5376 from rfl,trial_tail_5376]

private theorem trial_tail_4864 : trial_count 4864 26760=2750 := by
  rw [show 26760=256+26504 from rfl,trial_count_add,trial_block_4864,show 4864+256=5120 from rfl,trial_tail_5120]

private theorem trial_tail_4608 : trial_count 4608 27016=2778 := by
  rw [show 27016=256+26760 from rfl,trial_count_add,trial_block_4608,show 4608+256=4864 from rfl,trial_tail_4864]

private theorem trial_tail_4352 : trial_count 4352 27272=2807 := by
  rw [show 27272=256+27016 from rfl,trial_count_add,trial_block_4352,show 4352+256=4608 from rfl,trial_tail_4608]

private theorem trial_tail_4096 : trial_count 4096 27528=2837 := by
  rw [show 27528=256+27272 from rfl,trial_count_add,trial_block_4096,show 4096+256=4352 from rfl,trial_tail_4352]

private theorem trial_tail_3840 : trial_count 3840 27784=2869 := by
  rw [show 27784=256+27528 from rfl,trial_count_add,trial_block_3840,show 3840+256=4096 from rfl,trial_tail_4096]

private theorem trial_tail_3584 : trial_count 3584 28040=2899 := by
  rw [show 28040=256+27784 from rfl,trial_count_add,trial_block_3584,show 3584+256=3840 from rfl,trial_tail_3840]

private theorem trial_tail_3328 : trial_count 3328 28296=2933 := by
  rw [show 28296=256+28040 from rfl,trial_count_add,trial_block_3328,show 3328+256=3584 from rfl,trial_tail_3584]

private theorem trial_tail_3072 : trial_count 3072 28552=2962 := by
  rw [show 28552=256+28296 from rfl,trial_count_add,trial_block_3072,show 3072+256=3328 from rfl,trial_tail_3328]

private theorem trial_tail_2816 : trial_count 2816 28808=2992 := by
  rw [show 28808=256+28552 from rfl,trial_count_add,trial_block_2816,show 2816+256=3072 from rfl,trial_tail_3072]

private theorem trial_tail_2560 : trial_count 2560 29064=3026 := by
  rw [show 29064=256+28808 from rfl,trial_count_add,trial_block_2560,show 2560+256=2816 from rfl,trial_tail_2816]

private theorem trial_tail_2304 : trial_count 2304 29320=3059 := by
  rw [show 29320=256+29064 from rfl,trial_count_add,trial_block_2304,show 2304+256=2560 from rfl,trial_tail_2560]

private theorem trial_tail_2048 : trial_count 2048 29576=3092 := by
  rw [show 29576=256+29320 from rfl,trial_count_add,trial_block_2048,show 2048+256=2304 from rfl,trial_tail_2304]

private theorem trial_tail_1792 : trial_count 1792 29832=3123 := by
  rw [show 29832=256+29576 from rfl,trial_count_add,trial_block_1792,show 1792+256=2048 from rfl,trial_tail_2048]

private theorem trial_tail_1536 : trial_count 1536 30088=3159 := by
  rw [show 30088=256+29832 from rfl,trial_count_add,trial_block_1536,show 1536+256=1792 from rfl,trial_tail_1792]

private theorem trial_tail_1280 : trial_count 1280 30344=3194 := by
  rw [show 30344=256+30088 from rfl,trial_count_add,trial_block_1280,show 1280+256=1536 from rfl,trial_tail_1536]

private theorem trial_tail_1024 : trial_count 1024 30600=3229 := by
  rw [show 30600=256+30344 from rfl,trial_count_add,trial_block_1024,show 1024+256=1280 from rfl,trial_tail_1280]

private theorem trial_tail_768 : trial_count 768 30856=3266 := by
  rw [show 30856=256+30600 from rfl,trial_count_add,trial_block_768,show 768+256=1024 from rfl,trial_tail_1024]

private theorem trial_tail_512 : trial_count 512 31112=3304 := by
  rw [show 31112=256+30856 from rfl,trial_count_add,trial_block_512,show 512+256=768 from rfl,trial_tail_768]

private theorem trial_tail_256 : trial_count 256 31368=3347 := by
  rw [show 31368=256+31112 from rfl,trial_count_add,trial_block_256,show 256+256=512 from rfl,trial_tail_512]

private theorem trial_tail_0 : trial_count 0 31624=3402 := by
  rw [show 31624=256+31368 from rfl,trial_count_add,trial_block_0,show 0+256=256 from rfl,trial_tail_256]

theorem bounded_primes_length__sieve_construction : bounded_primes.length<3999 := by
  have h : bounded_primes.length=trial_count 0 31624 := by
    simp only [bounded_primes,trial_count,List.range_eq_range']
  rw [h,trial_tail_0]
  decide

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
