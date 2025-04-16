import ast
import subprocess
from openai import OpenAI
from dotenv import load_dotenv
import random
import os
import random
from datasets import load_dataset
import numpy as np

gsm8k = load_dataset("openai/gsm8k", "main")
example = gsm8k['train'][0]['question']


load_dotenv()
client = OpenAI()

print("Loading Client...\n")


def getExamples(num_examples=3):
    print("Getting Examples...\n")
    dataset = load_dataset("openai/gsm8k", "main")["train"]
    samples = random.sample(list(dataset), num_examples)
    examples_text = "\n\n".join(f"Example {i+1}:\n{ex['question']}" for i, ex in enumerate(samples))
    return examples_text

def generateProblem(client, numExamplesToPull=3):
    examplesGen = getExamples(numExamplesToPull)
    print("Generating Problem...\n")

    system_prompt = (
        "You are a math word problem generator. Your goal is to create math problems "
        "that resemble the style of the GSM8K dataset. Each problem must have a unique numeric solution.\n\n"
        "Here are a few examples:\n\n"
        f"{examplesGen}\n\n"
        "Now generate a new, original problem that follows this same format. Do not include the answer or explanation."
        "Do not copy any examples in the GSM8K dataset"
    )

    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": "Generate a new math problem."}
        ]
    )
    print(response.choices[0].message.content.strip() + "\n")
    return response.choices[0].message.content.strip()


def convert_to_lean(client, problem_text):
    print("Converting to Lean...\n")
    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": (
                "You are a Lean 4 proof assistant. Translate math word problems into Lean 4 code that proves there is a unique numeric answer. "
                "Do not include any explanation—output only valid Lean 4 code. ONLY the Lean 4 code that checks its uniqueness"
                "IMPORTANT: Use Lean 4 style imports (i.e. use 'import Mathlib.Data.Nat.Basic' instead of 'import data.nat.basic'). "
                "Lean 4 code does not use 'begin' or 'end' CONFIRM there is not begin or end syntax"
                "Lean 4 code does not have '∃!' only '∃'"
                "You are to provide code to ensure that the problem only has one solution, NOT to provide code to show the answer to the problem"
            )},
            {"role": "user", "content": f"Convert this word problem to a Lean 4 proof:\n\n{problem_text}"}
        ]
    )

    text = response.choices[0].message.content
    print(text)
    return text
    # if "```lean" in text:
    #     print(response.choices[0].message.content)
    #     return text.split("```lean")[1].split("```")[0].strip()
    # return ""

def create_system_equations(client, code):
    print("Creatiing Systems of Equations \n")
    response = client.chat.completions.create(
        model = "gpt-4",
        messages=[
            {"role": "system", "content": (
                "You are a Math Genius. Your task is to take the problem and generate a system of equations out of it"
                "Do NOT include any additional comments or explanation-output, just the system of equations"
            )},
            {"role": "user", "content": f"Create a system of equations using this problem:\n\n{code}"}
        ]
    )
    print(response.choices[0].message.content)
    text = response.choices[0].message.content
    return text

def create_Matrix(client, systems):
    print("Creatiing Systems of Equations \n")
    response = client.chat.completions.create(
    model = "gpt-4",
    messages=[
            {"role": "system", "content": (
                "You are a Math Genius. Your task is to turn that system of equations into a matrix"
                "Do NOT include any additional comments or explanation-output, just the matrix"
             )},
            {"role": "user", "content": f"Create a matrix using:\n\n{systems}"}
        ]
    )
    print(response.choices[0].message.content + "\n")
    text = response.choices[0].message.content
    return text


def determine_uniqueness(matrix):
    isUnique = False
    try:
        matrixList = ast.literal_eval(matrix)
    except Exception as e:
        raise ValueError(f"Error parsing matrix text: {e}")
    arr = np.array(matrixList)
    rank = np.linalg.matrix_rank(arr)
    full_rank = min(arr.shape)
    print("The rank of the matrix is:", rank,"\n")

    if(full_rank == rank):
        isUnique = True
        print("The problem is unique")
    else:
        determine_uniqueness(create_Matrix(client,create_system_equations(client, generateProblem(client))))


# convert_to_lean(client, generateProblem(client))

determine_uniqueness(create_Matrix(client,create_system_equations(client, generateProblem(client))))
