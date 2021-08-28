import random as R


# Three Doors problem / Monty Hall
#
# There are three closed doors. Behind one door is a car. Behind the
# other doors is nothing. Pick one door. The quiz master knows where
# the car is and opens one of the doors you have not picked and behind
# which there is no car. Now you can choose to stic kto your first
# choice or to switch to the remaining closed door. What is the best
# choice, assuming you would like to have the car?

DOORS = {1,2,3}

def pick(door_set):
    # set.pop() is not really random, so these lines do not work:
    #d = door_set.pop()
    #door_set.add(d)

    # therefore we use R.choice
    d = R.choice(tuple(door_set))
    return d

def stick(door1, qm_door):
    # Stick to door1
    return door1

def switch(door1, qm_door):
    # pick the door that is neither door1 nor qm_door
    return pick(DOORS - {door1, qm_door})

def round(strategy):
    assert DOORS == {1,2,3}
    car_door = pick(DOORS)
    door1 = pick(DOORS)
    other_doors = DOORS - {door1}
    qm_door = pick(other_doors - {car_door})
    chosen_door = strategy(door1, qm_door)
    return 1 if chosen_door == car_door else 0

def run_rounds(num_rounds):
    n = num_rounds
    num_stick_success = sum(round(stick) for n in range(n))
    num_switch_success = num_rounds - num_stick_success 
    return (num_stick_success, num_switch_success)


if __name__ == '__main__':

    stick(100)
    switch(100)

# The simulation shows that the switch strategy is more
# successful. Here is an explanation. After you have picked a door,
# the chance you picked the door with the car behind it is 1/3. Of the
# two remaining doors, the quiz master picks a door where he knows
# there is no car. If we assume the car is behind one of these
# remaining doors, the "chance" to switch to the right door is 1 (you
# switch to the only closed door left). So, under this assumption, the
# switch-strategy has a chance of 2/3 * 1 on success, whereas the
# stick-strategy has a chance of 1/3 * 0. On the other hand, if you
# picked the right door in the first place, with 1/3 chance, the
# chance of the stick-strategy to be successful after the quiz master
# opens one of the remaining doors is 1/3 * 1, whereas the chance of
# the switch strategy is 2/3*0. Summarizing this, the stick-strategy
# has 1/3 + 0 = 1/3 chance on success and the switch-strategy has 2/3
# + 0 = 2/3 chance on success.
