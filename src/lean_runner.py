


def convert_to_lean(client, problem_text):
    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": (
                "You are a Lean 4 proof assistant. "
                "Translate math word problems into Lean 4 code that proves there is a unique numeric answer. "
                "Use `∃!` for uniqueness. Wrap the result in ```lean ``` code fences."
            )},
            {"role": "user", "content": f"Convert this word problem to a Lean proof:\n\n{problem_text}"}
        ]
    )

    text = response.choices[0].message.content
    if "```lean" in text:
        return text.split("```lean")[1].split("```")[0].strip()
    return ""

def check_with_lean(code: str, filename="proof.lean"):
    with open(filename, "w") as f:
        f.write(code)

    result = subprocess.run(["lean", filename], capture_output=True, text=True)
    return result.returncode == 0, result.stderr


def problem_feedback_loop(client, max_attempts=5):
    for attempt in range(max_attempts):
        print(f"\n🔁 Attempt {attempt+1}")
        
        problem = generate_gsm8k_problem(client)
        print(f"📝 Problem:\n{problem}\n")

        lean_code = convert_to_lean(client, problem)
        if not lean_code:
            print("⚠️ No Lean code generated.")
            continue

        success, stderr = check_with_lean(lean_code)

        if success:
            print("✅ Valid problem! Unique solution confirmed by Lean.")
            return problem
        else:
            print("❌ Problem was invalid or had multiple solutions.")
            print("🧠 Sending feedback to regenerate.")
    
    print("❌ Could not generate a valid problem after several attempts.")
    return None



def run_lean_code(code: str, filename="proof.lean") -> tuple[bool, str, str]:
    filepath = os.path.join(os.getcwd(), filename)
    with open(filepath, "w") as f:
        f.write(code)

    result = subprocess.run(["lean", filepath], capture_output=True, text=True)
    success = result.returncode == 0
    return success, result.stdout, result.stderr