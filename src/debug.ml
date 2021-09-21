(*pp cppo *)

#ifdef DEBUG
#define dprintf(args) printf args
#else
#define dprintf(args) ()
#endif

#ifdef VERBOSE
#define vprintf(args) printf args
#else
#define vprintf(args) ()
#endif

#ifdef ASSERTS
#define dassert(arg) (if not (arg) then Printf.eprintf "Assertion failed: %s\n" STRINGIFY(arg); assert (arg))
#else
#define dassert(arg) ()
#endif

exception Assertion_failed of string

let puts str = IO.nwrite IO.stdout (str ^ "\n"); IO.flush IO.stdout