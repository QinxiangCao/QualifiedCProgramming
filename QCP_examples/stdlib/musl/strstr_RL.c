/*@ Extern Coq (program :: * => * => *) (unit :: *) */
/*@ Extern Coq
 (safeExec : {S} {A} -> (S -> Prop) -> program S A -> (A -> S -> Prop) -> Prop)
 (result_state : {S} {A} -> (S -> Prop) -> program S A -> (A -> S -> Prop))
 (ATrue : {A} -> A -> Prop)
 (return : {S} {A} -> A -> program S A)
 (maketuple : {A} {B} -> A -> B -> (A * B))
 (maxsuf_fwd : list Z -> program unit (Z * Z))
 (maxsuf_rev : list Z -> program unit (Z * Z))
 (maxsuf_fwd_from_state : list Z -> Z -> Z -> Z -> Z -> program unit (Z * Z))
 (maxsuf_rev_from_state : list Z -> Z -> Z -> Z -> Z -> program unit (Z * Z))
 (critical_factorization_prog : list Z -> program unit (Z * Z)) */
/*@ Printing Coq Name program := MonadErr.M */
/*@ Import Coq From SimpleC.EE.stdlib.musl.monad Require Import two_way_rel_lib */
/*@ Import Coq From MonadLib Require Import MonadLib */
/*@ Import Coq Export StateRelMonadErr MonadNotation */
/*@ Import Coq Local Open Scope monad */
/* Verification-only header adaptation.
 * The upstream source includes <string.h> and <stdint.h> here. QCP cannot
 * parse those system headers, so this region declares only the types and
 * external functions used below. All executable differences from upstream
 * are separately marked at the three short loops, the direct byte reads,
 * the BITOP macro, and the table-fill loop below.
 * The size_t binding models a 64-bit unsigned target; uint16_t and uint32_t
 * retain their exact widths. This adaptation must be audited against the
 * chosen musl target ABI before claiming source-level verification.
 */
/*@ include strategies "strstr_rel_cleanup.strategies" */
/* QCP proof dependency: generated VCs use predicates defined in this
 * case library. This annotation changes no C declaration or execution.
 */
/*@ Import Coq Require Import SimpleC.EE.stdlib.musl.strstr_rel_lib */
/*@ Import Coq Require Import SimpleC.EE.stdlib.musl.monad.factorization_refinement */

/*@ Import Coq Require Import SimpleC.EE.stdlib.musl.monad.search_cursor_refinement */
/*@ Extern Coq (search_cursor : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (search_right_cursor : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
 (search_left_cursor : list Z -> list Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop) */
typedef unsigned long long size_t;
typedef unsigned short uint16_t;
typedef unsigned int uint32_t;
/*@ Extern Coq (UCharArray::full : Z -> Z -> list Z -> Assertion)
				(UInt64Array::full : Z -> Z -> list Z -> Assertion)
				(UInt64Array::mixed_full : Z -> Z -> list (option Z) -> Assertion)
				(Zlength : {A} -> list A -> Z)
				(Znth : {A} -> Z -> list A -> A -> A)
				(app : {A} -> list A -> list A -> list A)
				(cons : {A} -> A -> list A -> list A)
				(nil : {A} -> list A)
				(sublist : {A} -> Z -> Z -> list A -> list A)
				(nonzero_bytes : list Z -> Prop)
				(strstr_result : list Z -> list Z -> Z -> Z -> Prop)
				(no_match_before : list Z -> list Z -> Z -> Prop)
				(strchr_result : list Z -> Z -> Z -> Z -> Prop)
				(rolling2 : list Z -> Z -> Z -> Prop)
				(needle2 : list Z -> Z -> Prop)
				(rolling3 : list Z -> Z -> Z -> Prop)
				(needle3 : list Z -> Z -> Prop)
				(rolling4 : list Z -> Z -> Z -> Prop)
				(needle4 : list Z -> Z -> Prop)
				(memcmp_zero : list Z -> Z -> Z -> Z -> Z -> Prop)
				(memchr_zero_result : list Z -> Z -> Z -> Z -> Z -> Prop)
				(byteset_prefix : list Z -> Z -> list Z -> Prop)
				(shift_prefix : list Z -> Z -> list Z -> Prop)
				(matched_range : list Z -> list Z -> Z -> Z -> Z -> Prop)
				(right_half_matched : list Z -> list Z -> Z -> Z -> Z -> Z -> Prop)
				(maxsuf_cut_index64 : Z -> Z -> Prop)
				(critical_search_split : list Z -> Z -> Z -> Prop)
				(periodic_memory_state : list Z -> Z -> Z -> Z -> Prop)
*/
/* The library calls are external proof dependencies.  The memchr contract
 * records early stopping at NUL even when count exceeds the remaining
 * string object; that behavior still requires a separate implementation or
 * platform audit before an end-to-end C claim. */
char *strchr(const char *s, int c)
	/*@ With (hs : list Z)
		Require nonzero_bytes(hs) && 0 < c && c < 256 &&
				UCharArray::full(s, Zlength(hs)+1, app(hs, cons(0, nil)))
		Ensure strchr_result(hs, c, s@pre, __return) &&
			   UCharArray::full(s@pre, Zlength(hs)+1, app(hs, cons(0, nil)))
	*/
	;
int memcmp(const void *a, const void *b, size_t count)
	/*@ With (bytes : list Z)
		Require exists off,
				b == pointer_offset(a, off, unsigned char) &&
				0 <= off && off+count <= Zlength(bytes)+1 &&
				UCharArray::full(a, Zlength(bytes)+1,
					app(bytes, cons(0, nil)))
		Ensure exists off,
			   b@pre == pointer_offset(a@pre, off, unsigned char) &&
			   0 <= off && off+count <= Zlength(bytes)+1 &&
			   memcmp_zero(app(bytes, cons(0, nil)),
						   0, off, count, __return) &&
			   UCharArray::full(a@pre, Zlength(bytes)+1,
				   app(bytes, cons(0, nil)))
	*/
	;
void *memchr(const void *s, int c, size_t count)
	/*@ With (suffix : list Z)
		Require c == 0 && nonzero_bytes(suffix) &&
				UCharArray::full(s, Zlength(suffix)+1,
					app(suffix, cons(0, nil)))
		Ensure memchr_zero_result(suffix, s@pre, 0, count, __return) &&
			   UCharArray::full(s@pre, Zlength(suffix)+1,
				   app(suffix, cons(0, nil)))
	*/
	;

static char *twobyte_strstr(const unsigned char *h, const unsigned char *n)
/*@ With (hs ns : list Z)
	Require nonzero_bytes(hs) && nonzero_bytes(ns) &&
			Zlength(ns) == 2 && 2 <= Zlength(hs) &&
			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	Ensure strstr_result(hs, ns, h@pre, __return) &&
		   UCharArray::full(h@pre, Zlength(hs)+1, app(hs, cons(0, nil))) *
		   UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
*/
{
	uint16_t nw = n[0] << 8 | n[1], hw = h[0] << 8 | h[1];
	/* QCP verification rewrite of the original empty-body loop:
	 * for (h++; *h && hw != nw; hw = hw<<8 | *++h);
	 * The body below increments h before reading *h, as the original
	 * for-update expression does. Source equivalence is an open audit item.
	 */
	/* QCP byte-read spelling: h[0] is exactly *h at the current h. */
	/* The rolling word covers the two-byte window ending at h.  Earlier
	 * window starts are already excluded from the first-match result. */
	/*@ Inv Assert exists i,
			h == h@pre + i && n == n@pre &&
			1 <= i && i <= Zlength(hs) &&
			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			rolling2(hs, i, hw) && needle2(ns, nw) &&
			no_match_before(hs, ns, i-1) &&
			UCharArray::full(h@pre, i,
				sublist(0, i, app(hs, cons(0, nil)))) *
			UCharArray::full(h, Zlength(hs)+1-i,
				sublist(i, Zlength(hs)+1, app(hs, cons(0, nil)))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	*/
	for (h++; h[0] && hw != nw;)
	{
		h = h + 1;
		/* Repartition the same bytes at the advanced cursor.  The loop
		 * guard excludes the terminator at the old cursor. */
		/*@ Assert exists j,
				h == h@pre + j && n == n@pre &&
				2 <= j && j <= Zlength(hs) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				rolling2(hs, j-1, hw) && needle2(ns, nw) &&
				no_match_before(hs, ns, j-1) &&
				UCharArray::full(h@pre, j,
					sublist(0, j, app(hs, cons(0, nil)))) *
				UCharArray::full(h, Zlength(hs)+1-j,
					sublist(j, Zlength(hs)+1, app(hs, cons(0, nil)))) *
				UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
		*/
		hw = hw << 8 | h[0];
	}
	return h[0] ? (char *)h - 1 : 0;
}

static char *threebyte_strstr(const unsigned char *h, const unsigned char *n)
/*@ With (hs ns : list Z)
	Require nonzero_bytes(hs) && nonzero_bytes(ns) &&
			Zlength(ns) == 3 && 3 <= Zlength(hs) &&
			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	Ensure strstr_result(hs, ns, h@pre, __return) &&
		   UCharArray::full(h@pre, Zlength(hs)+1, app(hs, cons(0, nil))) *
		   UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
*/
{
	uint32_t nw = (uint32_t)n[0] << 24 | n[1] << 16 | n[2] << 8;
	uint32_t hw = (uint32_t)h[0] << 24 | h[1] << 16 | h[2] << 8;
	/* QCP verification rewrite of the original empty-body loop:
	 * for (h+=2; *h && hw != nw; hw = (hw|*++h)<<8);
	 * The body below increments h before reading *h, as the original
	 * for-update expression does. Source equivalence is an open audit item.
	 */
	/* QCP byte-read spelling: h[0] is exactly *h at the current h. */
	/*@ Inv Assert exists i,
			h == h@pre + i && n == n@pre &&
			2 <= i && i <= Zlength(hs) &&
			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			rolling3(hs, i, hw) && needle3(ns, nw) &&
			no_match_before(hs, ns, i-2) &&
			UCharArray::full(h@pre, i,
				sublist(0, i, app(hs, cons(0, nil)))) *
			UCharArray::full(h, Zlength(hs)+1-i,
				sublist(i, Zlength(hs)+1, app(hs, cons(0, nil)))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	*/
	for (h += 2; h[0] && hw != nw;)
	{
		h = h + 1;
		/*@ Assert exists j,
				h == h@pre + j && n == n@pre &&
				3 <= j && j <= Zlength(hs) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				rolling3(hs, j-1, hw) && needle3(ns, nw) &&
				no_match_before(hs, ns, j-2) &&
				UCharArray::full(h@pre, j,
					sublist(0, j, app(hs, cons(0, nil)))) *
				UCharArray::full(h, Zlength(hs)+1-j,
					sublist(j, Zlength(hs)+1, app(hs, cons(0, nil)))) *
				UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
		*/
		hw = (hw | h[0]) << 8;
	}
	return h[0] ? (char *)h - 2 : 0;
}

static char *fourbyte_strstr(const unsigned char *h, const unsigned char *n)
/*@ With (hs ns : list Z)
	Require nonzero_bytes(hs) && nonzero_bytes(ns) &&
			Zlength(ns) == 4 && 4 <= Zlength(hs) &&
			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	Ensure strstr_result(hs, ns, h@pre, __return) &&
		   UCharArray::full(h@pre, Zlength(hs)+1, app(hs, cons(0, nil))) *
		   UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
*/
{
	uint32_t nw = (uint32_t)n[0] << 24 | n[1] << 16 | n[2] << 8 | n[3];
	uint32_t hw = (uint32_t)h[0] << 24 | h[1] << 16 | h[2] << 8 | h[3];
	/* QCP verification rewrite of the original empty-body loop:
	 * for (h+=3; *h && hw != nw; hw = hw<<8 | *++h);
	 * The body below increments h before reading *h, as the original
	 * for-update expression does. Source equivalence is an open audit item.
	 */
	/* QCP byte-read spelling: h[0] is exactly *h at the current h. */
	/*@ Inv Assert exists i,
			h == h@pre + i && n == n@pre &&
			3 <= i && i <= Zlength(hs) &&
			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			rolling4(hs, i, hw) && needle4(ns, nw) &&
			no_match_before(hs, ns, i-3) &&
			UCharArray::full(h@pre, i,
				sublist(0, i, app(hs, cons(0, nil)))) *
			UCharArray::full(h, Zlength(hs)+1-i,
				sublist(i, Zlength(hs)+1, app(hs, cons(0, nil)))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	*/
	for (h += 3; h[0] && hw != nw;)
	{
		h = h + 1;
		/*@ Assert exists j,
				h == h@pre + j && n == n@pre &&
				4 <= j && j <= Zlength(hs) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				rolling4(hs, j-1, hw) && needle4(ns, nw) &&
				no_match_before(hs, ns, j-3) &&
				UCharArray::full(h@pre, j,
					sublist(0, j, app(hs, cons(0, nil)))) *
				UCharArray::full(h, Zlength(hs)+1-j,
					sublist(j, Zlength(hs)+1, app(hs, cons(0, nil)))) *
				UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
		*/
		hw = hw << 8 | h[0];
	}
	return h[0] ? (char *)h - 3 : 0;
}

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MIN(a, b) ((a) < (b) ? (a) : (b))

/* QCP verification rewrite: upstream BITOP uses sizeof *(a) twice.
 * Both calls below pass byteset, whose element type is size_t. On the
 * selected 64-bit ABI sizeof(size_t) = 8; QCP fails to parse sizeof in
 * these expressions, so the literal 8 is C-equivalent on this target.
 * The upstream source is unchanged.
 */
#define BITOP(a, b, op) \
	((a)[(size_t)(b) / (8 * 8)] op(size_t) 1 << ((size_t)(b) % (8 * 8)))

static char *twoway_strstr(const unsigned char *h, const unsigned char *n)
/*@ With (hs ns : list Z)
	Require nonzero_bytes(hs) && nonzero_bytes(ns) &&
			5 <= Zlength(ns) && 4 <= Zlength(hs) &&
			Zlength(ns) <= 18446744073709551615 &&
			Zlength(hs) <= 18446744073709551615 &&
			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	Ensure strstr_result(hs, ns, h@pre, __return) &&
		   UCharArray::full(h@pre, Zlength(hs)+1, app(hs, cons(0, nil))) *
		   UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
*/
{
	const unsigned char *z;
	size_t l, ip, jp, k, p, ms, p0, mem, mem0;
	/* QCP parser adaptation: sizeof(size_t) = 8 on the selected ABI. */
	size_t byteset[32 / 8] = {0};
	/* Verification representation: zero initialization gives the partial
	 * musl table a total logical list.  BITOP gates every shift read, so an
	 * entry that was not written by the preprocessing loop is never observed. */
	size_t shift[256] = {0};

	/* Computing length of needle and fill shift table.
	 * QCP verification rewrite of the upstream comma expression:
	 * for (l=0; n[l] && h[l]; l++)
	 *     BITOP(byteset, n[l], |=), shift[n[l]] = l+1;
	 * The comma operator sequences the byteset update before the shift
	 * update. n[l] and the index arithmetic have no side effects, so the
	 * explicit read/OR/write has the same C effect as the compound |=.
	 */
	/* The prefix n[0..l) has been inspected.  Its byteset and shift table
	 * contents are retained as logical lists for later first-match proof.
	 * The long-needle entry bound is unchanged while l advances.
	 * Pure list lengths mirror the fixed C arrays for split VCs.
	 * The needle length bound follows from its owned UChar array object
	 * (including the terminator); it keeps l+1 below 2^64. */
	/*@ Inv Assert exists bs sh,
			h == h@pre && n == n@pre &&
			5 <= Zlength(ns) &&
			Zlength(ns) <= 18446744073709551615 &&
			0 <= l && l <= Zlength(ns) && l <= Zlength(hs) &&
			0 <= app(ns, cons(0, nil))[l] &&
			app(ns, cons(0, nil))[l] < 256 &&
			0 <= app(ns, cons(0, nil))[l]/(8*8) &&
			app(ns, cons(0, nil))[l]/(8*8) < 4 &&
			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			Zlength(bs) == 4 && Zlength(sh) == 256 &&
			byteset_prefix(ns, l, bs) && shift_prefix(ns, l, sh) &&
			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil))) *
			UInt64Array::full(byteset, 4, bs) *
			UInt64Array::full(shift, 256, sh) *
			has_permission(&z) * has_permission(&ip) *
			has_permission(&jp) * has_permission(&k) *
			has_permission(&p) * has_permission(&ms) *
			has_permission(&p0) * has_permission(&mem) *
			has_permission(&mem0)
	*/
	for (l = 0; n[l] && h[l]; l++)
	{
		byteset[(size_t)n[l] / (8 * 8)] =
			byteset[(size_t)n[l] / (8 * 8)] |
			((size_t)1 << ((size_t)n[l] % (8 * 8)));
		shift[n[l]] = l + 1;
	}
	if (n[l])
		return 0; /* hit the end of h */

	ip = -1;
	jp = 0;
	p = 1;
	k = 1;
	/*@ Inv Assert exists bs sh,
				safeExec(ATrue, maxsuf_fwd_from_state(ns, unsigned_last_nbits(ip+1, 64)-1, jp, k, p),
					result_state(ATrue, maxsuf_fwd(ns))) &&
			h == h@pre && n == n@pre &&
			5 <= l && l == Zlength(ns) && l <= Zlength(hs) &&
			(ip == 18446744073709551615 || ip < jp) &&
			0 <= jp && jp <= l &&
			0 <= unsigned_last_nbits(ip+k, 64) &&
			unsigned_last_nbits(ip+k, 64) < l &&
			0 <= unsigned_last_nbits(jp+k, 64) &&
			1 <= k && k <= p && p <= l &&
			p + unsigned_last_nbits(ip+1, 64) <= l &&
				jp+k <= l &&
				unsigned_last_nbits(ip+1, 64) <= jp &&
			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			byteset_prefix(ns, l, bs) && shift_prefix(ns, l, sh) &&
			0 <= ip &&
			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil))) *
			UInt64Array::full(byteset, 4, bs) *
			UInt64Array::full(shift, 256, sh) *
			has_permission(&z) * has_permission(&ms) *
			has_permission(&p0) * has_permission(&mem) *
			has_permission(&mem0)
	*/
	while (jp + k < l)
	{
		if (n[ip + k] == n[jp + k])
		{
			if (k == p)
			{
				jp += p;
				k = 1;
			}
			else
				k++;
		}
		else if (n[ip + k] > n[jp + k])
		{
			jp += k;
			k = 1;
			p = jp - ip;
		}
		else
		{
			ip = jp;
			jp++;
			p = 1;
			k = 1;
		}
	}
	ms = ip;
	p0 = p;

	ip = -1;
	jp = 0;
	p = 1;
	k = 1;
	/*@ Inv Assert exists bs sh,
				safeExec(ATrue, maxsuf_rev_from_state(ns, unsigned_last_nbits(ip+1, 64)-1, jp, k, p),
					result_state(ATrue, maxsuf_rev(ns))) &&
				safeExec(ATrue, return(maketuple(unsigned_last_nbits(ms+1, 64)-1, p0)),
					result_state(ATrue, maxsuf_fwd(ns))) &&
			h == h@pre && n == n@pre &&
			5 <= l && l == Zlength(ns) && l <= Zlength(hs) &&
			(ip == 18446744073709551615 || ip < jp) &&
			0 <= jp && jp <= l &&
			0 <= unsigned_last_nbits(ip+k, 64) &&
			unsigned_last_nbits(ip+k, 64) < l &&
			0 <= unsigned_last_nbits(jp+k, 64) &&
			1 <= k && k <= p && p <= l &&
			p + unsigned_last_nbits(ip+1, 64) <= l &&
				jp+k <= l &&
				unsigned_last_nbits(ip+1, 64) <= jp &&
		(ms == 18446744073709551615 || ms < l) &&
		0 <= ms &&
		1 <= p0 && p0 <= l &&
			p0 + unsigned_last_nbits(ms+1, 64) <= l+1 &&

			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			byteset_prefix(ns, l, bs) && shift_prefix(ns, l, sh) &&
			0 <= ip &&

			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil))) *
			UInt64Array::full(byteset, 4, bs) *
			UInt64Array::full(shift, 256, sh) *
			has_permission(&z) * has_permission(&mem) *
			has_permission(&mem0)
	*/
	while (jp + k < l)
	{
		if (n[ip + k] == n[jp + k])
		{
			if (k == p)
			{
				jp += p;
				k = 1;
			}
			else
				k++;
		}
		else if (n[ip + k] < n[jp + k])
		{
			jp += k;
			k = 1;
			p = jp - ip;
		}
		else
		{
			ip = jp;
			jp++;
			p = 1;
			k = 1;
		}
	}
	mem0 = ms;
	mem = p;
	if (ip + 1 > ms + 1)
		ms = ip;
	else
		p = p0;

	/*@ Assert exists bs sh,
				safeExec(ATrue, return(maketuple(unsigned_last_nbits(ms+1, 64), p)),
					result_state(ATrue, critical_factorization_prog(ns))) &&
			h == h@pre && n == n@pre &&
			5 <= l && l == Zlength(ns) && l <= Zlength(hs) &&
			Zlength(app(ns, cons(0, nil))) == l+1 &&
			(ip == 18446744073709551615 || ip < l) &&
			0 <= jp && jp <= l && 1 <= k &&
			1 <= p0 && p0 <= l &&
			1 <= p && p <= l &&
			1 <= mem && mem <= l &&
			maxsuf_cut_index64(ms, l) &&
			0 <= unsigned_last_nbits(ms+1, 64) &&
			p + unsigned_last_nbits(ms+1, 64) <= l+1 &&

			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			byteset_prefix(ns, l, bs) && shift_prefix(ns, l, sh) &&
			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil))) *
			UInt64Array::full(byteset, 4, bs) *
			UInt64Array::full(shift, 256, sh) *
			has_permission(&z) * has_permission(&mem0)
	*/
	if (memcmp(n, n + p, ms + 1))
	{
		mem0 = 0;
		p = MAX(ms, l - ms - 1) + 1;
	}
	else
		mem0 = l - p;
	mem = 0;

	/* Initialize incremental end-of-haystack pointer */
	z = h;

	/* Search loop */
	/* pos is the next candidate start; end is the known scanned frontier.
	 * The three array resources partition the original unchanged haystack.
	 * Every candidate before pos has already failed.  The object-size bound
	 * follows from ownership of the original NUL-terminated byte array and
	 * makes pointer differences below 2^64 exact. */
	/*@ Inv Assert exists pos end bs sh,
			h == h@pre + pos && z == h@pre + end &&
			n == n@pre && l == Zlength(ns) &&
			Zlength(hs) <= 18446744073709551615 &&
			0 <= pos && pos <= end && end <= Zlength(hs) &&
			5 <= l && l <= Zlength(hs) &&
			no_match_before(hs, ns, pos) &&
			matched_range(hs, ns, pos, 0, mem) &&
			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			byteset_prefix(ns, l, bs) && shift_prefix(ns, l, sh) &&
			nonzero_bytes(sublist(end, Zlength(hs), hs)) &&
			(ms == 18446744073709551615 || (0 <= ms && ms < l)) &&
			(ip == 18446744073709551615 || ip < l) &&
			1 <= p && p <= l && 1 <= p0 && p0 <= l &&
			0 <= jp && jp <= l && 0 <= k &&
			0 <= mem && mem <= l && 0 <= mem0 && mem0 <= l &&
			periodic_memory_state(ns, p, mem, mem0) &&
			critical_search_split(ns, unsigned_last_nbits(ms+1, 64), p) &&
			search_cursor(hs, ns, unsigned_last_nbits(ms+1, 64), p, mem0, pos, mem) &&
			UCharArray::full(h@pre, pos,
				sublist(0, pos, hs)) *
			UCharArray::full(h, end-pos,
				sublist(pos, end, hs)) *
			UCharArray::full(z,
				Zlength(sublist(end, Zlength(hs), hs))+1,
				app(sublist(end, Zlength(hs), hs), cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1,
				app(ns, cons(0, nil))) *
			UInt64Array::full(byteset, 4, bs) *
			UInt64Array::full(shift, 256, sh)
	*/
	for (;;)
	{
		/* Update incremental end-of-haystack pointer */
		if (z - h < l)
		{
			/* Fast estimate for MAX(l,63) */
			size_t grow = l | 63;
			const unsigned char *z2 = memchr(z, 0, grow);
			if (z2)
			{
				z = z2;
				if (z - h < l)
					return 0;
			}
			else
				z += grow;
		}

		/* Check last byte first; advance by shift on mismatch */
		/* Repartition at the new scan frontier.  Every path reaching the
		 * table lookup has at least l bytes from h through z. */
		/*@ Assert exists pos end bs sh,
				h == h@pre + pos && z == h@pre + end &&
				n == n@pre && l == Zlength(ns) &&
				Zlength(hs) <= 18446744073709551615 &&
				0 <= pos && pos <= end && end <= Zlength(hs) &&
				5 <= l && l <= end-pos &&
				0 <= sublist(pos, end, hs)[l-1] &&
				sublist(pos, end, hs)[l-1] < 256 &&
				0 <= sublist(pos, end, hs)[l-1]/(8*8) &&
				sublist(pos, end, hs)[l-1]/(8*8) < 4 &&
				no_match_before(hs, ns, pos) &&
				matched_range(hs, ns, pos, 0, mem) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				byteset_prefix(ns, l, bs) && shift_prefix(ns, l, sh) &&
				nonzero_bytes(sublist(end, Zlength(hs), hs)) &&
				(ms == 18446744073709551615 || (0 <= ms && ms < l)) &&
				(ip == 18446744073709551615 || ip < l) &&
				1 <= p && p <= l && 1 <= p0 && p0 <= l &&
				0 <= jp && jp <= l && 0 <= k &&
				0 <= mem && mem <= l && 0 <= mem0 && mem0 <= l &&
				periodic_memory_state(ns, p, mem, mem0) &&
				critical_search_split(ns, unsigned_last_nbits(ms+1, 64), p) &&
				search_cursor(hs, ns, unsigned_last_nbits(ms+1, 64), p, mem0, pos, mem) &&
				UCharArray::full(h@pre, pos,
					sublist(0, pos, hs)) *
				UCharArray::full(h, end-pos,
					sublist(pos, end, hs)) *
				UCharArray::full(z,
					Zlength(sublist(end, Zlength(hs), hs))+1,
					app(sublist(end, Zlength(hs), hs), cons(0, nil))) *
				UCharArray::full(n, Zlength(ns)+1,
					app(ns, cons(0, nil))) *
				UInt64Array::full(byteset, 4, bs) *
				UInt64Array::full(shift, 256, sh)
		*/
		if (BITOP(byteset, h[l - 1], &))
		{
			k = l - shift[h[l - 1]];
			if (k)
			{
				if (k < mem)
					k = mem;
				h += k;
				mem = 0;
				continue;
			}
		}
		else
		{
			h += l;
			mem = 0;
			continue;
		}

		/* Compare right half */
		/* The inspected right-half prefix agrees; the next read stays in
		 * the known haystack window whenever the needle byte is nonzero. */
		/*@ Inv Assert exists pos end bs sh,
				h == h@pre + pos && z == h@pre + end &&
				n == n@pre && l == Zlength(ns) &&
				0 <= pos && pos <= end && end <= Zlength(hs) &&
				5 <= l && l <= end-pos &&
				0 <= k && k <= l && k < Zlength(ns)+1 &&
				(app(ns, cons(0, nil))[k] != 0 => k < l) &&
				no_match_before(hs, ns, pos) &&
				matched_range(hs, ns, pos, 0, mem) &&
				right_half_matched(hs, ns, pos,
					unsigned_last_nbits(ms+1, 64), mem, k) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				byteset_prefix(ns, l, bs) && shift_prefix(ns, l, sh) &&
				nonzero_bytes(sublist(end, Zlength(hs), hs)) &&
				(ms == 18446744073709551615 || (0 <= ms && ms < l)) &&
				(ip == 18446744073709551615 || ip < l) &&
				1 <= p && p <= l && 1 <= p0 && p0 <= l &&
				0 <= jp && jp <= l &&
				0 <= mem && mem <= l && 0 <= mem0 && mem0 <= l &&
				periodic_memory_state(ns, p, mem, mem0) &&
				critical_search_split(ns, unsigned_last_nbits(ms+1, 64), p) &&
				search_right_cursor(hs, ns, unsigned_last_nbits(ms+1, 64), p, mem0, pos, mem, k) &&
				UCharArray::full(h@pre, pos,
					sublist(0, pos, hs)) *
				UCharArray::full(h, end-pos,
					sublist(pos, end, hs)) *
				UCharArray::full(z,
					Zlength(sublist(end, Zlength(hs), hs))+1,
					app(sublist(end, Zlength(hs), hs), cons(0, nil))) *
				UCharArray::full(n, Zlength(ns)+1,
					app(ns, cons(0, nil))) *
				UInt64Array::full(byteset, 4, bs) *
				UInt64Array::full(shift, 256, sh)
		*/
		for (k = MAX(ms + 1, mem); n[k] && n[k] == h[k]; k++)
			;
		if (n[k])
		{
			h += k - ms;
			mem = 0;
			continue;
		}
		/* Compare left half */
		/* k moves left through the remaining prefix; indices k-1 are valid
		 * whenever the loop guard k>mem holds. The remembered prefix [0,mem)
		 * stays matched while k walks left; together with [k,l), it covers
		 * the entire needle when k reaches mem. */
		/*@ Inv Assert exists pos end bs sh,
				h == h@pre + pos && z == h@pre + end &&
				n == n@pre && l == Zlength(ns) &&
				0 <= pos && pos <= end && end <= Zlength(hs) &&
				5 <= l && l <= end-pos &&
				0 <= mem && mem <= l && 0 <= k && k <= l &&
				k <= unsigned_last_nbits(ms+1, 64) &&
				no_match_before(hs, ns, pos) &&
				matched_range(hs, ns, pos, 0, mem) &&
				matched_range(hs, ns, pos, k, l) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				byteset_prefix(ns, l, bs) && shift_prefix(ns, l, sh) &&
				nonzero_bytes(sublist(end, Zlength(hs), hs)) &&
				(ms == 18446744073709551615 || (0 <= ms && ms < l)) &&
				(ip == 18446744073709551615 || ip < l) &&
				1 <= p && p <= l && 1 <= p0 && p0 <= l &&
				0 <= jp && jp <= l && 0 <= mem0 && mem0 <= l &&
				periodic_memory_state(ns, p, mem, mem0) &&
				critical_search_split(ns, unsigned_last_nbits(ms+1, 64), p) &&
				search_left_cursor(hs, ns, unsigned_last_nbits(ms+1, 64), p, mem0, pos, mem, k) &&
				UCharArray::full(h@pre, pos,
					sublist(0, pos, hs)) *
				UCharArray::full(h, end-pos,
					sublist(pos, end, hs)) *
				UCharArray::full(z,
					Zlength(sublist(end, Zlength(hs), hs))+1,
					app(sublist(end, Zlength(hs), hs), cons(0, nil))) *
				UCharArray::full(n, Zlength(ns)+1,
					app(ns, cons(0, nil))) *
				UInt64Array::full(byteset, 4, bs) *
				UInt64Array::full(shift, 256, sh)
		*/
		for (k = ms + 1; k > mem && n[k - 1] == h[k - 1]; k--)
			;
		if (k <= mem)
			return (char *)h;
		h += p;
		mem = mem0;
	}
}

char *strstr(const char *h, const char *n)
/*@ With (hs ns : list Z)
	Require 0 <= Zlength(hs) && 0 <= Zlength(ns) &&
			nonzero_bytes(hs) && nonzero_bytes(ns) &&
			UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
			UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	Ensure strstr_result(hs, ns, h@pre, __return) &&
		   UCharArray::full(h@pre, Zlength(hs)+1, app(hs, cons(0, nil))) *
		   UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
*/
{
	/* Return immediately on empty needle */
	/* QCP U8 read spelling: casting char * to unsigned char * preserves
	 * each byte address. Zero tests are identical; strchr interprets its
	 * character argument as unsigned char. No pointer or byte is changed.
	 */
	if (!((const unsigned char *)n)[0])
		return (char *)h;
	/* The nonzero first byte lies before the terminating NUL.  QCP's
	 * symbolic array opener needs this lower bound stated explicitly. */
	/*@ Assert h == h@pre && n == n@pre &&
				1 <= Zlength(ns) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				UCharArray::full(h, Zlength(hs)+1, app(hs, cons(0, nil))) *
				UCharArray::full(n, Zlength(ns)+1, app(ns, cons(0, nil)))
	*/

	/* Use faster algorithms for short needles */
	/* QCP byte-read spelling: n[0] is exactly *n at the current n. */
	h = strchr(h, ((const unsigned char *)n)[0]);
	if (!h || !((const unsigned char *)n)[1])
		return (char *)h;
	/* strchr found a nonzero first byte within the original haystack;
	 * the second nonzero needle byte lies before its terminator. The
	 * needle pointer is unchanged, so its resource keeps its entry base. */
	/*@ Assert exists i,
				h == h@pre + i && n == n@pre &&
				0 <= i && i < Zlength(hs) &&
				2 <= Zlength(ns) &&
				no_match_before(hs, ns, i) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				UCharArray::full(h@pre, i,
					sublist(0, i, app(hs, cons(0, nil)))) *
				UCharArray::full(h, Zlength(hs)+1-i,
					sublist(i, Zlength(hs)+1, app(hs, cons(0, nil)))) *
				UCharArray::full(n, Zlength(ns)+1,
					app(ns, cons(0, nil)))
	*/
	if (!((const unsigned char *)h)[1])
		return 0;
	/* The second haystack byte is nonzero, so this suffix contains at
	 * least two data bytes.  Name the suffix in the ordinary C-string
	 * shape expected by the short-helper contract. */
	/*@ Assert exists i,
				h == h@pre + i && n == n@pre &&
				0 <= i && i + 2 <= Zlength(hs) &&
				2 <= Zlength(ns) &&
				2 <= Zlength(sublist(i, Zlength(hs), hs)) &&
				(app(ns, cons(0, nil))[2] == 0 => Zlength(ns) == 2) &&
				(app(ns, cons(0, nil))[2] != 0 => 3 <= Zlength(ns)) &&
				no_match_before(hs, ns, i) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				nonzero_bytes(sublist(i, Zlength(hs), hs)) &&
				UCharArray::full(h@pre, i,
					sublist(0, i, app(hs, cons(0, nil)))) *
				UCharArray::full(h,
					Zlength(sublist(i, Zlength(hs), hs))+1,
					app(sublist(i, Zlength(hs), hs), cons(0, nil))) *
				UCharArray::full(n, Zlength(ns)+1,
					app(ns, cons(0, nil)))
	*/
	if (!((const unsigned char *)n)[2])
		return twobyte_strstr((void *)h, (void *)n);
	if (!((const unsigned char *)h)[2])
		return 0;
	/* A nonzero third haystack byte extends the same owned suffix. */
	/*@ Assert exists i,
				h == h@pre + i && n == n@pre &&
				0 <= i && i + 3 <= Zlength(hs) &&
				3 <= Zlength(sublist(i, Zlength(hs), hs)) &&
				3 <= Zlength(ns) &&
				(app(ns, cons(0, nil))[3] == 0 => Zlength(ns) == 3) &&
				(app(ns, cons(0, nil))[3] != 0 => 4 <= Zlength(ns)) &&
				no_match_before(hs, ns, i) &&
				nonzero_bytes(hs) && nonzero_bytes(ns) &&
				nonzero_bytes(sublist(i, Zlength(hs), hs)) &&
				UCharArray::full(h@pre, i,
					sublist(0, i, app(hs, cons(0, nil)))) *
				UCharArray::full(h,
					Zlength(sublist(i, Zlength(hs), hs))+1,
					app(sublist(i, Zlength(hs), hs), cons(0, nil))) *
				UCharArray::full(n, Zlength(ns)+1,
					app(ns, cons(0, nil)))
	*/
	if (!((const unsigned char *)n)[3])
		return threebyte_strstr((void *)h, (void *)n);
	if (!((const unsigned char *)h)[3])
		return 0;
	if (!((const unsigned char *)n)[4])
		return fourbyte_strstr((void *)h, (void *)n);

	return twoway_strstr((void *)h, (void *)n);
}
