#-------------------------------------------------------------------
#   IMPORTS
#-------------------------------------------------------------------
from datasets import load_dataset
from openai import OpenAI
from dotenv import load_dotenv

#Counter for how Many Trues
counter = 0

# Load the GSM8K training split
dataset = load_dataset("openai/gsm8k", "main", split="train")

# Select the first 1000 problems
subset = dataset.select(range(7473))

load_dotenv()
client = OpenAI()


#-------------------------------------------------------------------
#  FUNCTIONS
#-------------------------------------------------------------------
def check_Linear_System(client, problem):
    print("Checking... \n")

    system_prompt = (
        "You are a math genius. Tell me if this problem can be made into a system of equation"
        f"{problem}\n\n"
        "Do not include the answer or explanation."    
        "Only return True if the problem can be made into a system of equation. Return False if the problem cannot be made into a system of equation"
        )

    response = client.chat.completions.create(
        model="gpt-4",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": "Tell me in only True and False statements"}
        ]
    )
    print(response.choices[0].message.content.strip() + "\n")
    return response.choices[0].message.content.strip()

#-------------------------------------------------------------------
#   RUN CODE
#-------------------------------------------------------------------
for i in range(7473):
    if(check_Linear_System(client, subset[i]['question']) == 'True'):
        counter += 1

print(counter)