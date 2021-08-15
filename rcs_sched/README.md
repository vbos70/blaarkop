# Resource Scheduling

- The system contains 6 processeros: P0..P5.

- There are 5 jobs (processes/tasks): J1..J5.

- The jobs never end.

- A processor can execute at most 1 task at ant time.

- The time scale is irrelevant. We take seconds as the time unit, but
  any other unit works as well.

- S(Pi) is the state of a processor, where 0 <= i <= 5. It is
  is a pair (Jn, T0) where

  - Jn is a job (1 <= n <= 5), denoted by J(Pi)
  
  - T0 is a time: the time at which Pi started executing Jn, denoted
    by T0(Pi)

- Two processors Pi and Pj "mirror" each other / behave identically if
  S(Pi) == S(Pj), where 0 <= i,j <= 5.

- An allocation is a mapping from processors to jobs or None for
  unallocated processors. Allocations are denoted as follows:
  
      { P0 : J1, P1 : J2, P2: J3, P3: J4, P4: J5, P5: None }
  
  Here, P0 .. P4 are allocated to J1 .. J5, respectively and P5 is
  unallocated.

  The unallocated processors might be left out. So, the previous
  allocation is identical to this:
  
      { P0 : J1, P1 : J2, P2: J3, P3: J4, P4: J5 }
 
- The system state consists of all processor states:

      [S(P0), S(P1), S(P2), S(P3), S(P4), S(P5)]

- The current allocation can be derived from the system state:

      cur_alloc = { Pi : J(Pi) for 0 <= i <= 5 }
  
- The system state is updated by calling configure(alloc), where alloc
  is an allocation.
  
  For example, this configures P0 and P3:
  
      configure({ P0: J2, P3: J1} )

  The update occurs at atomically at a time T and it changes the
  processor states S(P0) and S(P3):
  
      J(P0) = J2
      T0(P0) = T
	  
	  J(P3) = J1
	  T0(P3) = T
	  
  All other processor states remain unchanged by this configure() call.

- Two calls to configure() never occur at the same time. If
  configure(alloc1) executes on T1 and configure(alloc2) on T2 and
  configure(alloc1) is done before configure(alloc2), then T1 < T2.

- If configure(alloc) is called

  1. all processors in alloc are switching contect.
  
  2. all jobs allocated in alloc are interrupted.


## Detection of processor faults

The processors in the system described above have random faults which
randomly lead to processing errors. This is observable by comparing
behaviour of mirrored processors. If the behaviour os mirrored
processors differs, a processing error has been detected.

To detect processing errors, it is therefore necessary to mirror
processors.

Once a processing error has occured on a processor Pi running job Jn,
the behaviour of the processor is erroneous / cannot be trusted until
a configure() call updates the state of the processor.


## Goal

Develop an algorithm that executes the 5 jobs on the 6 processors such
that any processing error is detected within 3 seconds and where jobs
are interrupted as little as possible.


## Example of an algorithm with 5 seconds processing error detection time

Select P5 as the (only) mirror processor.

1. initialize system:

   1. configure( { P0 : J1, P1 : J2, P2: J3, P3: J4, P4: J5, P5: None } )

   2. jobs = [J1, J2, J3, J4, J5]  # zero-indexed list of the jobs

   3. mirror = 0  # index into jobs 
	   
2. while True:  # main loop

   1.     configure( { P5: jobs[mirror] } )

   2.     mirror = (mirror + 1) mod 5

   3.     delay 1s

This algorithm initially allocates all jobs to the first 5
processors. A list-variable containing the jobs is created and a
mirror variable is defined epresenting an index into the
list-variable.

Then the main loop starts and it allocates P5 to the job running on
P0. Next, the mirrot index is incrased by 1 modulo 5. Finally, the
mian loop waits for 1 second.

### Fixing a Mistake

The algorithm above does not guarantee that S(P0) == S(P5) after the
configure() call on 2.1. The time T0(P0) is not necessarily the same
as T0(P5) after this call.

To fix this, reallocate the mirrored processor when P5 is
allocated. To this end, another list-variable is needed containing
processors [P0, P1, P2, P3, P4] (not P5). The index variable mirror is
now used both to identify the processor being mirrored and the job
running on the mirrored processor and P5.

1. initialize system:

   1. configure( { P0 : None, P1 : J2, P2: J3, P3: J4, P4: J5, P5: None } )
   
   2. processors = [ P0, P1, P2, P3, P4 ]

   3. jobs = [J1, J2, J3, J4, J5]  # zero-indexed list of the jobs

   4. mirror = 0  # index into jobs 
	   
2. while True:  # main loop

   1.     configure( { processors[mirror]: jobs[mirror], P5: jobs[mirror] } )

   2.     mirror = (mirror + 1) mod 5

   3.     delay 1s

